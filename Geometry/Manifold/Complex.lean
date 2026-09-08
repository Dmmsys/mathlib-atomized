/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Topology.LocallyConstant.Basic

/-! # Holomorphic functions on complex manifolds

Thanks to the rigidity of complex-differentiability compared to real-differentiability, there are
many results about complex manifolds with no analogue for manifolds over a general normed field. For
now, this file contains just two (closely related) such results:

## Main results

* `MDifferentiable.isLocallyConstant`: A complex-differentiable function on a compact complex
  manifold is locally constant.
* `MDifferentiable.exists_eq_const_of_compactSpace`: A complex-differentiable function on a compact
  preconnected complex manifold is constant.

## TODO

There is a whole theory to develop here.  Maybe a next step would be to develop a theory of
holomorphic vector/line bundles, including:
* the finite-dimensionality of the space of sections of a holomorphic vector bundle
* Siegel's theorem: for any `n + 1` formal ratios `g 0 / h 0`, `g 1 / h 1`, .... `g n / h n` of
  sections of a fixed line bundle `L` over a complex `n`-manifold, there exists a polynomial
  relationship `P (g 0 / h 0, g 1 / h 1, .... g n / h n) = 0`

Another direction would be to develop the relationship with sheaf theory, building the sheaves of
holomorphic and meromorphic functions on a complex manifold and proving algebraic results about the
stalks, such as the Weierstrass preparation theorem.

-/

public section

open scoped Manifold Topology Filter
open Function Set Filter Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- **Maximum modulus principle**: if `f : M → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. This is a manifold version of `Complex.norm_eventually_eq_of_isLocalMax`. -/
/-
**Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax {f : M -> F}
 {c : M} (hd : forallᶠ z in 𝓝 c, MDiffAt f z) (hc : IsLocalMax (norm ∘ f) c) : f
orallᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖
参数：hd : forallᶠ z in 𝓝 c, MDiffAt f z；hc : IsLocalMax (norm ∘ f) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.Boundaryless.range_eq_univ`：∀ {𝕜 : Type u_1} {inst : No
ntriviallyNormedField 𝕜} {E : Type u_2} {inst_1 : NormedAddCommGroup E}   {inst_
2 : NormedSpace 𝕜 E} {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_extChartAt_symm_nhdsWithin_range`：map_extChartAt_symm_nhdsWithin_ran
ge (x : M) : map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `mdifferentiableAt_iff_of_mem_source`：mdifferentiableAt_iff_of_mem_source
 [IsManifold I 1 M] [IsManifold I' 1 M'] {x' : M} {y : M'} (hx : x' in (chartAt 
H x).source) (hy : f x' i…
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `IsManifold.instOfNatWithTopENat_2`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
· 使用定理 `Complex.norm_eventually_eq_of_isLocalMax`：norm_eventually_eq_of_isLocalM
ax {f : E -> F} {c : E} (hd : forallᶠ z in 𝓝 c, DifferentiableAt Complex f z) (h
c : IsLocalMax (norm ∘ f) c) :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
**Maximum modulus principle**: if `f : M → F` is complex differentiable in a nei
ghborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constan
t in a neighborhood
of `c`. This is a manifold version of `Complex.norm_eventually_eq_of_isLocalMax`
.
-/
theorem Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax {f : M → F} {c : M}
    (hd : ∀ᶠ z in 𝓝 c, MDiffAt f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  set e := extChartAt I c
  have hI : range I = univ := ModelWithCorners.Boundaryless.range_eq_univ
  have H₁ : 𝓝[range I] (e c) = 𝓝 (e c) := by rw [hI, nhdsWithin_univ]
  have H₂ : map e.symm (𝓝 (e c)) = 𝓝 c := by
    rw [← map_extChartAt_symm_nhdsWithin_range (I := I) c, H₁]
  rw [← H₂, eventually_map]
  replace hd : ∀ᶠ y in 𝓝 (e c), DifferentiableAt ℂ (f ∘ e.symm) y := by
    have : e.target ∈ 𝓝 (e c) := H₁ ▸ extChartAt_target_mem_nhdsWithin c
    filter_upwards [this, Tendsto.eventually H₂.le hd] with y hyt hy₂
    have hys : e.symm y ∈ (chartAt H c).source := by
      rw [← extChartAt_source I c]
      exact (extChartAt I c).map_target hyt
    have hfy : f (e.symm y) ∈ (chartAt F (0 : F)).source := mem_univ _
    rw [mdifferentiableAt_iff_of_mem_source hys hfy, hI, differentiableWithinAt_univ,
      e.right_inv hyt] at hy₂
    exact hy₂.2
  convert! norm_eventually_eq_of_isLocalMax hd _
  · exact congr_arg f (extChartAt_to_inv _).symm
  · simpa only [e, IsLocalMax, IsMaxFilter, ← H₂, (· ∘ ·), extChartAt_to_inv] using! hc

/-!
### Functions holomorphic on a set
-/

namespace MDifferentiableOn

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
/-
**MDifferentiableOn.norm_eqOn_of_isPreconnected_of_isMaxOn** 是 Mathlib 中的一个定理，位于
命名空间 `MDifferentiableOn`。
形式化陈述：norm_eqOn_of_isPreconnected_of_isMaxOn {f : M -> F} {U : Set M} {c : M} (h
d : MDiff[U] f) (hc : IsPreconnected U) (ho : IsOpen U) (hcU : c in U) (hm : IsM
axOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const M ‖f c‖) U
参数：hd : MDiff[U] f；hc : IsPreconnected U；ho : IsOpen U；hcU : c in U；hm : IsMaxOn
 (norm ∘ f) U c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhds_iff`：eventually_mem_nhds_iff : (forallᶠ x' in 𝓝 x, s
 in 𝓝 x') ↔ s in 𝓝 x
· 使用定理 `MDifferentiableOn.mdifferentiableAt`：MDifferentiableOn.mdifferentiableAt
 (h : MDiff[s] f) (hx : s in 𝓝 x) : MDiffAt f x
· 使用定理 `Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax`：Complex.n
orm_eventually_eq_of_mdifferentiableAt_of_isLocalMax {f : M -> F} {c : M} (hd : 
forallᶠ z in 𝓝 c, MDiffAt f z) (hc : IsLocalMax (no…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `MDifferentiableOn.continuousOn`：MDifferentiableOn.continuousOn (h : MDif
f[s] f) : ContinuousOn f s
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsPreconnected.subset_left_of_subset_union`：IsPreconnected.subset_left_o
f_subset_union (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hsuv : s su
bseteq u union v) (hsu : (s inte…

--- 原说明 ---
**Maximum modulus principle** on a connected set. Let `U` be a (pre)connected op
en set in a
complex normed space. Let `f : E → F` be a function that is complex differentiab
le on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for
 all `x ∈ U`.
-/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : M → F} {U : Set M} {c : M}
    (hd : MDiff[U] f) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const M ‖f c‖) U := by
  set V := {z ∈ U | ‖f z‖ = ‖f c‖}
  suffices U ⊆ V from fun x hx ↦ (this hx).2
  have hVo : IsOpen V := by
    refine isOpen_iff_mem_nhds.2 fun x hx ↦ inter_mem (ho.mem_nhds hx.1) ?_
    replace hm : IsLocalMax (‖f ·‖) x :=
      mem_of_superset (ho.mem_nhds hx.1) fun z hz ↦ (hm hz).out.trans_eq hx.2.symm
    replace hd : ∀ᶠ y in 𝓝 x, MDiffAt f y :=
      (eventually_mem_nhds_iff.2 (ho.mem_nhds hx.1)).mono fun z ↦ hd.mdifferentiableAt
    exact (Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hm).mono fun _ ↦
      (Eq.trans · hx.2)
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  set W := U ∩ {z | ‖f z‖ = ‖f c‖}ᶜ
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hUVW : U ⊆ V ∪ W := fun x hx => (eq_or_ne ‖f x‖ ‖f c‖).imp (.intro hx) (.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`. -/
/-
**MDifferentiableOn.eqOn_of_isPreconnected_of_isMaxOn_norm** 是 Mathlib 中的一个定理，位于
命名空间 `MDifferentiableOn`。
形式化陈述：eqOn_of_isPreconnected_of_isMaxOn_norm [StrictConvexSpace Real F] {f : M -
> F} {U : Set M} {c : M} (hd : MDiff[U] f) (hc : IsPreconnected U) (ho : IsOpen 
U) (hcU : c in U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const M (f c)) U
参数：hd : MDiff[U] f；hc : IsPreconnected U；ho : IsOpen U；hcU : c in U；hm : IsMaxOn
 (norm ∘ f) U c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableOn.norm_eqOn_of_isPreconnected_of_isMaxOn`：norm_eqOn_of_i
sPreconnected_of_isMaxOn {f : M -> F} {U : Set M} {c : M} (hd : MDiff[U] f) (hc 
: IsPreconnected U) (ho : IsOpen U) (hcU : c i…
· 使用定理 `MDifferentiableOn.add`：MDifferentiableOn.add {s : Set M} (hf : MDiff[s] 
f) (hg : MDiff[s] g) : MDiff[s] (f + g)
· 使用定理 `mdifferentiableOn_const`：mdifferentiableOn_const : MDiff[s] (fun _ : M =
> c)
· 使用定理 `IsMaxOn.norm_add_self`：IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c
) : IsMaxOn (fun x => ‖f x + f c‖) s c
· 使用定理 `eq_of_norm_eq_of_norm_add_eq`：eq_of_norm_eq_of_norm_add_eq (h₁ : ‖x‖ = ‖
y‖) (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SameRay.norm_add`：norm_add (h : SameRay Real x y) : ‖x + y‖ = ‖x‖ + ‖y‖
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Maximum modulus principle** on a connected set. Let `U` be a (pre)connected op
en set in a
complex normed space.  Let `f : E → F` be a function that is complex differentia
ble on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all
 `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`.
-/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm [StrictConvexSpace ℝ F] {f : M → F} {U : Set M}
    {c : M} (hd : MDiff[U] f) (hc : IsPreconnected U) (ho : IsOpen U)
    (hcU : c ∈ U) (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const M (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := hd.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm hx
  have hd' : MDiff[U] (f · + f c) := hd.add mdifferentiableOn_const
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    hd'.norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

/-- If a function `f : M → F` from a complex manifold to a complex normed space is holomorphic on a
(pre)connected compact open set, then it is a constant on this set. -/
/-
**MDifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen** 是 Mathlib 中的一个
定理，位于命名空间 `MDifferentiableOn`。
形式化陈述：apply_eq_of_isPreconnected_isCompact_isOpen {f : M -> F} {U : Set M} {a b 
: M} (hd : MDiff[U] f) (hpc : IsPreconnected U) (hc : IsCompact U) (ho : IsOpen 
U) (ha : a in U) (hb : b in U) : f a = f b
参数：hd : MDiff[U] f；hpc : IsPreconnected U；hc : IsCompact U；ho : IsOpen U；ha : a 
in U；hb : b in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `MDifferentiableOn.continuousOn`：MDifferentiableOn.continuousOn (h : MDif
f[s] f) : ContinuousOn f s
· 使用定理 `MDifferentiableOn.norm_eqOn_of_isPreconnected_of_isMaxOn`：norm_eqOn_of_i
sPreconnected_of_isMaxOn {f : M -> F} {U : Set M} {c : M} (hd : MDiff[U] f) (hc 
: IsPreconnected U) (ho : IsOpen U) (hcU : c i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `DifferentiableWithinAt.sub_const`：DifferentiableWithinAt.sub_const (hf :
 DifferentiableWithinAt 𝕜 f s x) (c : F) : DifferentiableWithinAt 𝕜 (fun y => f 
y - c) s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
If a function `f : M → F` from a complex manifold to a complex normed space is h
olomorphic on a
(pre)connected compact open set, then it is a constant on this set.
-/
theorem apply_eq_of_isPreconnected_isCompact_isOpen {f : M → F} {U : Set M} {a b : M}
    (hd : MDiff[U] f) (hpc : IsPreconnected U) (hc : IsCompact U)
    (ho : IsOpen U) (ha : a ∈ U) (hb : b ∈ U) : f a = f b := by
  -- Subtract `f b` to avoid the assumption `[StrictConvexSpace ℝ F]`
  wlog hb₀ : f b = 0 generalizing f
  -- TODO: Add `MDifferentiableOn.sub` etc
  · have hd' : MDiff[U] (f · - f b) := fun x hx ↦
      ⟨(hd x hx).1.sub continuousWithinAt_const, (hd x hx).2.sub_const _⟩
    simpa [sub_eq_zero] using this hd' (sub_self _)
  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
  have : ∀ x ∈ U, ‖f x‖ = ‖f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hd hpc ho hcU hc
  rw [hb₀, ← norm_eq_zero, this a ha, ← this b hb, hb₀, norm_zero]

end MDifferentiableOn

/-!
### Functions holomorphic on the whole manifold

Lemmas in this section were generalized from `𝓘(ℂ, E)` to an unspecified boundaryless
model so that it works, e.g., on a product of two manifolds without a boundary. This can break
`apply MDifferentiable.apply_eq_of_compactSpace`, use
`apply MDifferentiable.apply_eq_of_compactSpace (I := I)` instead or dot notation on an existing
`MDifferentiable` hypothesis.
-/

namespace MDifferentiable

variable [CompactSpace M]

/-- A holomorphic function on a compact complex manifold is locally constant. -/
/-
**MDifferentiable.isLocallyConstant** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiable`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{F : Type u_2} [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℂ F] {H :
 Type u_3} [inst_4 : TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundar
yless]   {M : Type u_4} [inst_6 : TopologicalSpace M] [inst_7 : ChartedSpace H M
] [IsManifold I 1 M] [CompactSpace M]   {f : M → F}, MDiff f → IsLocallyConstant
 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.of_constant_on_preconnected_clopens`：of_constant_on_pr
econnected_clopens [LocallyConnectedSpace X] {f : X -> Y} (h : forall U : Set X,
 IsPreconnected U -> IsClopen U -> forall x…
· 使用定理 `ChartedSpace.locallyConnectedSpace`：ChartedSpace.locallyConnectedSpace [
LocallyConnectedSpace H] : LocallyConnectedSpace M
· 使用定理 `Homeomorph.locallyConnectedSpace`：locallyConnectedSpace [i : LocallyConn
ectedSpace Y] (h : X ≃ₜ Y) : LocallyConnectedSpace X
· 使用定理 `instLocallyConnectedSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[LocallyPathConnectedSpace X], LocallyConnectedSpace X
· 使用定理 `LocallyConvexSpace.toLocallyPathConnectedSpace`：∀ (E : Type u_2) [inst :
 AddCommGroup E] [inst_1 : TopologicalSpace E] [IsTopologicalAddGroup E]   [inst
_3 : _root_.Module ℝ E] [ContinuousS…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MDifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen`：apply_eq_
of_isPreconnected_isCompact_isOpen {f : M -> F} {U : Set M} {a b : M} (hd : MDif
f[U] f) (hpc : IsPreconnected U) (hc : IsCompact U)…
· 使用定理 `MDifferentiable.mdifferentiableOn`：MDifferentiable.mdifferentiableOn (h 
: MDiff f) : MDiff[s] f
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClopen.isClosed`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X
}, IsClopen s → IsClosed s
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s

--- 原说明 ---
A holomorphic function on a compact complex manifold is locally constant.
-/
protected theorem isLocallyConstant {f : M → F} (hf : MDiff f) :
    IsLocallyConstant f :=
  haveI : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  IsLocallyConstant.of_constant_on_preconnected_clopens fun _ hpc hclo _a ha _b hb ↦
    hf.mdifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen hpc
      hclo.isClosed.isCompact hclo.isOpen hb ha

/-- A holomorphic function on a compact connected complex manifold is constant. -/
/-
**MDifferentiable.apply_eq_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `MDifferent
iable`。
形式化陈述：apply_eq_of_compactSpace [PreconnectedSpace M] {f : M -> F} (hf : MDiff f)
 (a b : M) : f a = f b
参数：hf : MDiff f；a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.apply_eq_of_preconnectedSpace`：apply_eq_of_preconnecte
dSpace [PreconnectedSpace X] {f : X -> Y} (hf : IsLocallyConstant f) (x y : X) :
 f x = f y
· 使用定理 `MDifferentiable.isLocallyConstant`：∀ {E : Type u_1} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℂ E] {F : Type u_2} [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…

--- 原说明 ---
A holomorphic function on a compact connected complex manifold is constant.
-/
theorem apply_eq_of_compactSpace [PreconnectedSpace M] {f : M → F}
    (hf : MDiff f) (a b : M) : f a = f b :=
  hf.isLocallyConstant.apply_eq_of_preconnectedSpace _ _

/-- A holomorphic function on a compact connected complex manifold is the constant function `f ≡ v`,
for some value `v`. -/
/-
**MDifferentiable.exists_eq_const_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `MDi
fferentiable`。
形式化陈述：exists_eq_const_of_compactSpace [PreconnectedSpace M] {f : M -> F} (hf : M
Diff f) : exists v : F, f = Function.const M v
参数：hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocallyConstant.exists_eq_const`：exists_eq_const [PreconnectedSpace X]
 [Nonempty Y] {f : X -> Y} (hf : IsLocallyConstant f) : exists y, f = Function.c
onst X y
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `MDifferentiable.isLocallyConstant`：∀ {E : Type u_1} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℂ E] {F : Type u_2} [inst_2 : NormedAddCommGroup
 F]   [inst_3 : NormedS…

--- 原说明 ---
A holomorphic function on a compact connected complex manifold is the constant f
unction `f ≡ v`,
for some value `v`.
-/
theorem exists_eq_const_of_compactSpace [PreconnectedSpace M] {f : M → F} (hf : MDiff f) :
    ∃ v : F, f = Function.const M v :=
  hf.isLocallyConstant.exists_eq_const

end MDifferentiable

