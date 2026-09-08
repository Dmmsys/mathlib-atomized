/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Rolle

/-!
# Rolle's Theorem

In this file we prove Rolle's Theorem. The theorem says that for a function `f : ℝ → ℝ` such that

* $f$ is differentiable on an open interval $(a, b)$, $a < b$;
* $f$ is continuous on the corresponding closed interval $[a, b]$;
* $f(a) = f(b)$,

there exists a point $c∈(a, b)$ such that $f'(c)=0$.

We prove four versions of this theorem.

* `exists_hasDerivAt_eq_zero` is closest to the statement given above. It assumes that at every
  point $x ∈ (a, b)$ function $f$ has derivative $f'(x)$, then concludes that $f'(c)=0$ for some
  $c∈(a, b)$.
* `exists_deriv_eq_zero` deals with `deriv f` instead of an arbitrary function `f'` and a predicate
  `HasDerivAt`; since we use zero as the "junk" value for `deriv f c`, this version does not
  assume that `f` is differentiable on the open interval.
* `exists_hasDerivAt_eq_zero'` is similar to `exists_hasDerivAt_eq_zero` but instead of assuming
  continuity on the closed interval $[a, b]$ it assumes that $f$ tends to the same limit as $x$
  tends to $a$ from the right and as $x$ tends to $b$ from the left.
* `exists_deriv_eq_zero'` relates to `exists_deriv_eq_zero` as `exists_hasDerivAt_eq_zero'`
  relates to `exists_hasDerivAt_eq_zero`.

## References

* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);

## Tags

local extremum, Rolle's Theorem
-/

public section

open Set Filter Topology

variable {f f' : ℝ → ℝ} {a b l : ℝ}

/-- **Rolle's Theorem** `HasDerivAt` version -/
/-
**exists_hasDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (
hfI : f a = f b) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) : exists c 
in Ioo a b, f' c = 0
参数：hab : a < b；hfc : ContinuousOn f (Icc a b)；hfI : f a = f b；hff' : forall x in
 Ioo a b, HasDerivAt f (f' x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `exists_isLocalExtr_Ioo`：exists_isLocalExtr_Ioo (hab : a < b) (hfc : Cont
inuousOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, IsLocalExtr f c
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsLocalExtr.hasDerivAt_eq_zero`：IsLocalExtr.hasDerivAt_eq_zero (h : IsLo
calExtr f a) : HasDerivAt f f' a -> f' = 0

--- 原说明 ---
**Rolle's Theorem** `HasDerivAt` version
-/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version -/
@[wikidata Q193286]
/-
**exists_deriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI :
 f a = f b) : exists c in Ioo a b, deriv f c = 0
参数：hab : a < b；hfc : ContinuousOn f (Icc a b)；hfI : f a = f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isLocalExtr_Ioo`：exists_isLocalExtr_Ioo (hab : a < b) (hfc : Cont
inuousOn f (Icc a b)) (hfI : f a = f b) : exists c in Ioo a b, IsLocalExtr f c
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsLocalExtr.deriv_eq_zero`：IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f 
a) : deriv f a = 0

--- 原说明 ---
**Rolle's Theorem** `deriv` version
-/
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`. -/
/-
**exists_hasDerivAt_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivAt_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) 
(hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : forall x in Ioo a b, HasDerivAt f (f' x
) x) : exists c in Ioo a b, f' c = 0
参数：hab : a < b；hfa : Tendsto f (𝓝[>] a) (𝓝 l)；hfb : Tendsto f (𝓝[<] b) (𝓝 l)；hff
' : forall x in Ioo a b, HasDerivAt f (f' x) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `exists_isLocalExtr_Ioo_of_tendsto`：exists_isLocalExtr_Ioo_of_tendsto (ha
b : a < b) (hfc : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb 
: Tendsto f (𝓝[<] b) (𝓝…
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `IsLocalExtr.hasDerivAt_eq_zero`：IsLocalExtr.hasDerivAt_eq_zero (h : IsLo
calExtr f a) : HasDerivAt f f' a -> f' = 0

--- 原说明 ---
**Rolle's Theorem**, a version for a function on an open interval: if `f` has de
rivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`.
-/
theorem exists_hasDerivAt_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo_of_tendsto hab
    (fun x hx ↦ (hff' x hx).continuousAt.continuousWithinAt) hfa hfb
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
/-
**exists_deriv_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) (hfb 
: Tendsto f (𝓝[<] b) (𝓝 l)) : exists c in Ioo a b, deriv f c = 0
参数：hab : a < b；hfa : Tendsto f (𝓝[>] a) (𝓝 l)；hfb : Tendsto f (𝓝[<] b) (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_hasDerivAt_eq_zero'`：exists_hasDerivAt_eq_zero' (hab : a < b) (hf
a : Tendsto f (𝓝[>] a) (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : forall x 
in Ioo a b, HasD…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0

--- 原说明 ---
**Rolle's Theorem**, a version for a function on an open interval: if `f` has th
e same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This v
ersion
does not require differentiability of `f` because we define `deriv f c = 0` when
ever `f` is not
differentiable at `c`.
-/
theorem exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) : ∃ c ∈ Ioo a b, deriv f c = 0 := by
  by_cases! h : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x
  · exact exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : ∃ x ∈ Ioo a b, ¬DifferentiableAt ℝ f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩
