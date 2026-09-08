/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Topology.UniformSpace.OfFun

/-!
# Uniform structure induced by an absolute value

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/

@[expose] public section

open Set Function Filter Uniformity

namespace AbsoluteValue

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {R : Type*} [CommRing R] (abv : AbsoluteValue R 𝕜)

/-- The uniform structure coming from an absolute value. -/
@[instance_reducible]
/-
**AbsoluteValue.uniformSpace** 是 Mathlib 中的一个定义，位于命名空间 `AbsoluteValue`。
形式化陈述：uniformSpace : UniformSpace R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform structure coming from an absolute value.
-/
def uniformSpace : UniformSpace R :=
  .ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun _ _ _ => (abv.sub_le _ _ _).trans_eq (add_comm _ _))
    fun ε ε0 => ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩
/-
**AbsoluteValue.hasBasis_uniformity** 是 Mathlib 中的一个定理，位于命名空间 `AbsoluteValue`。
形式化陈述：hasBasis_uniformity : 𝓤[abv.uniformSpace].HasBasis ((0 : 𝕜) < ·) fun ε => 
{ p : R × R | abv (p.2 - p.1) < ε }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.hasBasis_ofFun`：hasBasis_ofFun [AddCommMonoid M] [LinearOrd
er M] (h₀ : exists x : M, 0 < x) (d : X -> X -> M) (refl : forall x, d x x = 0) 
(symm : forall x …
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem hasBasis_uniformity :
    𝓤[abv.uniformSpace].HasBasis ((0 : 𝕜) < ·) fun ε => { p : R × R | abv (p.2 - p.1) < ε } :=
  UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _

end AbsoluteValue

