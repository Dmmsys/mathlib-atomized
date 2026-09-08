/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Notation

/-!
# Holomorphicity of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are holomorphic on the upper half plane, which is stated as being
MDifferentiable.
-/

public section

noncomputable section

open UpperHalfPlane Filter Function Complex Manifold CongruenceSubgroup

namespace EisensteinSeries

/-- Auxiliary lemma showing that for any `k : ℤ` the function `z → 1/(c*z+d)^k` is
differentiable on `{z : ℂ | 0 < z.im}`. -/
/-
**EisensteinSeries.div_linear_zpow_differentiableOn** 是 Mathlib 中的一个引理，位于命名空间 `E
isensteinSeries`。
形式化陈述：div_linear_zpow_differentiableOn (k : Int) (a : Fin 2 -> Int) : Differenti
ableOn Complex (fun z : Complex => (a 0 * z + a 1) ^ (-k)) {z : Complex | 0 < z.
im}
参数：k : Int；a : Fin 2 -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `DifferentiableOn.zpow`：DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f 
t) (h : (forall x in t, f x != 0) ∨ 0 <= m) : DifferentiableOn 𝕜 (fun x => f x ^
 m) t
· 使用定理 `DifferentiableOn.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `DifferentiableOn.const_mul`：DifferentiableOn.const_mul (ha : Differentia
bleOn 𝕜 a s) (b : 𝔸) : DifferentiableOn 𝕜 (fun y => b * a y) s
· 使用定理 `differentiableOn_id`：differentiableOn_id : DifferentiableOn 𝕜 id s
· 使用定理 `UpperHalfPlane.linear_ne_zero`：linear_ne_zero {cd : Fin 2 -> Real} (τ : 
ℍ) (h : cd != 0) : (cd 0 : Complex) * τ + cd 1 != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.comp_ne_zero_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : Zero β] [inst_1 : Zero γ] (f : α → β) {g : β → γ},   Function.Injectiv
e g → g 0 = 0 →…
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `differentiableOn_const`：differentiableOn_const (c : F) : DifferentiableO
n 𝕜 (fun _ => c) s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Auxiliary lemma showing that for any `k : ℤ` the function `z → 1/(c*z+d)^k` is
differentiable on `{z : ℂ | 0 < z.im}`.
-/
lemma div_linear_zpow_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => (a 0 * z + a 1) ^ (-k)) {z : ℂ | 0 < z.im} := by
  rcases ne_or_eq a 0 with ha | rfl
  · apply DifferentiableOn.zpow
    · fun_prop
    · left
      exact fun z hz ↦ linear_ne_zero ⟨z, hz⟩
        ((comp_ne_zero_iff _ Int.cast_injective Int.cast_zero).mpr ha)
  · simp only [Pi.zero_apply, Int.cast_zero, zero_mul, add_zero]
    apply differentiableOn_const

/-- Auxiliary lemma showing that for any `k : ℤ` and `(a : Fin 2 → ℤ)`
the extension of `eisSummand` is differentiable on `{z : ℂ | 0 < z.im}`. -/
/-
**EisensteinSeries.eisSummand_extension_differentiableOn** 是 Mathlib 中的一个引理，位于命名
空间 `EisensteinSeries`。
形式化陈述：eisSummand_extension_differentiableOn (k : Int) (a : Fin 2 -> Int) : Diffe
rentiableOn Complex (↑ₕeisSummand k a) {z : Complex | 0 < z.im}
参数：k : Int；a : Fin 2 -> Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.congr`：DifferentiableOn.congr (h : DifferentiableOn 𝕜 f
 s) (h' : forall x in s, f₁ x = f x) : DifferentiableOn 𝕜 f₁ s
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `EisensteinSeries.div_linear_zpow_differentiableOn`：div_linear_zpow_diffe
rentiableOn (k : Int) (a : Fin 2 -> Int) : DifferentiableOn Complex (fun z : Com
plex => (a 0 * z + a 1) ^ (-k)) {z : Co…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `UpperHalfPlane.comp_ofComplex`：comp_ofComplex (f : ℍ -> Complex) (z : ℍ)
 : (↑ₕf) z = f z

--- 原说明 ---
Auxiliary lemma showing that for any `k : ℤ` and `(a : Fin 2 → ℤ)`
the extension of `eisSummand` is differentiable on `{z : ℂ | 0 < z.im}`.
-/
lemma eisSummand_extension_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) :
    DifferentiableOn ℂ (↑ₕeisSummand k a) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.congr (div_linear_zpow_differentiableOn k a)
  intro z hz
  lift z to ℍ using hz
  apply comp_ofComplex

/-- Eisenstein series are MDifferentiable (i.e. holomorphic functions from `ℍ → ℂ`). -/
/-
**EisensteinSeries.eisensteinSeriesSIF_mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间
 `EisensteinSeries`。
形式化陈述：eisensteinSeriesSIF_mdifferentiable {k : Int} {N : Nat} (hk : 3 <= k) (a :
 Fin 2 -> ZMod N) : MDiff (eisensteinSeriesSIF a k)
参数：hk : 3 <= k；a : Fin 2 -> ZMod N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `TendstoLocallyUniformlyOn.differentiableOn`：∀ {E : Type u_1} {ι : Type u
_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] {U : Set ℂ} {φ : Fi
lter ι}   {F : ι → ℂ → E} {f : ℂ…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformlyOn`：eisensteinS
eries_tendstoLocallyUniformlyOn {k : Int} {N : Nat} (hk : 3 <= k) (a : Fin 2 -> 
ZMod N) : TendstoLocallyUniformlyOn (fun (s : Fin…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `DifferentiableOn.fun_sum`：DifferentiableOn.fun_sum (h : forall i in u, D
ifferentiableOn 𝕜 (A i) s) : DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s
· 使用引理 `EisensteinSeries.eisSummand_extension_differentiableOn`：eisSummand_exten
sion_differentiableOn (k : Int) (a : Fin 2 -> Int) : DifferentiableOn Complex (↑
ₕeisSummand k a) {z : Complex | 0 < z.im}
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `UpperHalfPlane.comp_ofComplex`：comp_ofComplex (f : ℍ -> Complex) (z : ℍ)
 : (↑ₕf) z = f z
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用定理 `DifferentiableAt.mdifferentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `UpperHalfPlane.mdifferentiable_coe`：mdifferentiable_coe : MDiff ((↑) : ℍ
 -> Complex)

--- 原说明 ---
Eisenstein series are MDifferentiable (i.e. holomorphic functions from `ℍ → ℂ`).
-/
theorem eisensteinSeriesSIF_mdifferentiable {k : ℤ} {N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    MDiff (eisensteinSeriesSIF a k) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕeisensteinSeriesSIF a k) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z ↦ (comp_ofComplex (eisensteinSeriesSIF a k) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (eisensteinSeries_tendstoLocallyUniformlyOn hk a).differentiableOn
    (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun _ _ ↦ eisSummand_extension_differentiableOn _ _) isOpen_upperHalfPlaneSet

@[deprecated (since := "2026-02-09")]
alias eisensteinSeries_SIF_MDifferentiable := eisensteinSeriesSIF_mdifferentiable

end EisensteinSeries

