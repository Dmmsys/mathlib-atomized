/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives of compositions

In this file we specialize Faà di Bruno's formula to one-dimensional domain
to deduce formulae for `iteratedDerivWithin k (g ∘ f) s x` for `k = 2` and `k = 3`.

We use
- `vcomp` for lemmas about the composition of `g : E → F` with `f : 𝕜 → E`;
- `scomp` for lemmas about the composition of `g : 𝕜 → E` with `f : 𝕜 → 𝕜`;
- `comp` for lemmas about the composition of `g : 𝕜 → 𝕜` with `f : 𝕜 → 𝕜`.

## TODO

- What `UniqueDiffOn` assumptions can be discarded?
- In case of dimension 1 (and, more generally, in case of symmetric iterated derivatives),
  some terms are equal.
  Add versions of Faà di Bruno's formula that take the symmetries into account.
- Can we generalize `scomp`/`comp` to `f : 𝕜 → 𝕜'`,
  where `𝕜'` is a normed algebra over `𝕜`? E.g., `𝕜 = ℝ`, `𝕜' = ℂ`.

Before starting to work on these TODOs, please contact Yury Kudryashov
who may have partial progress towards some of them.
-/

public section

open Function Set
open scoped ContDiff

section vcomp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {g : E → F} {f : 𝕜 → E} {s : Set 𝕜} {t : Set E} {x : 𝕜} {n : ℕ∞ω} {i : ℕ}

/-
**iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition (hg : ContDiffWithinA
t 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs :
 UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) (hi : i <= n) : iteratedDe
rivWithin i (g ∘ f) s x = ∑ c : OrderedFinpartition i, iteratedFDerivWithin 𝕜 c.
length g t (f x) fun j => iteratedDerivWithin (c.partSize j) f s x
参数：hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_comp`：iteratedFDerivWithin_comp {t : Set F} (hg : C
ontDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDif
fOn 𝕜 t) (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `ContinuousMultilinearMap.instIsAddApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → A
ddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i, iteratedFDerivWithin 𝕜 c.length g t (f x) fun j ↦
        iteratedDerivWithin (c.partSize j) f s x := by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_comp hg hf ht hs hx hst hi]
  simp [FormalMultilinearSeries.taylorComp, ftaylorSeriesWithin,
    OrderedFinpartition.applyOrderedFinpartition_apply, comp_def]
/-
**iteratedDeriv_vcomp_eq_sum_orderedFinpartition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hg : ContDiffAt 𝕜 n g (f x
)) (hf : ContDiffAt 𝕜 n f x) (hi : i <= n) : iteratedDeriv i (g ∘ f) x = ∑ c : O
rderedFinpartition i, iteratedFDeriv 𝕜 c.length g (f x) fun j => iteratedDeriv (
c.partSize j) f x
参数：hg : ContDiffAt 𝕜 n g (f x)；hf : ContDiffAt 𝕜 n f x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition`：iteratedDerivWithi
n_vcomp_eq_sum_orderedFinpartition (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : C
ontDiffWithinAt 𝕜 n f s x) (ht : UniqueDif…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i, iteratedFDeriv 𝕜 c.length g (f x) fun j ↦
        iteratedDeriv (c.partSize j) f x := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _) hi

set_option backward.isDefEq.respectTransparency false in
/-
**iteratedDerivWithin_vcomp_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_vcomp_two (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : 
ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx 
: x in s) (hst : MapsTo f s t) : iteratedDerivWithin 2 (g ∘ f) s x = iteratedFDe
rivWithin 𝕜 2 g t (f x) (fun _ => derivWithin f s x) + fderivWithin 𝕜 g t (f x) 
(iteratedDerivWithin 2 f s x)
参数：hg : ContDiffWithinAt 𝕜 2 g t (f x)；hf : ContDiffWithinAt 𝕜 2 f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition`：iteratedDerivWithi
n_vcomp_eq_sum_orderedFinpartition (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : C
ontDiffWithinAt 𝕜 n f s x) (ht : UniqueDif…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Fintype.sum_sigma`：∀ {ι : Type u_9} {α : ι → Type u_7} {M : Type u_8} [i
nst : Fintype ι] [inst_1 : (i : ι) → Fintype (α i)]   [inst_2 : AddCommMonoid M]
 (f : S…
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
· 使用定理 `Fintype.sum_unique`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Unique ι] (f : ι → M),   ∑ x, f x = f defaul
t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.forall_fin_two`：∀ {p : Fin 2 → Prop}, (∀ (i : Fin 2), p i) ↔ p 0 ∧ p
 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_one`：iteratedDerivWithin_one : iteratedDerivWithin 1
 f s = derivWithin f s
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `iteratedFDerivWithin_one_apply`：iteratedFDerivWithin_one_apply (h : Uniq
ueDiffWithinAt 𝕜 s x) (m : Fin 1 -> E) : iteratedFDerivWithin 𝕜 1 f s x m = fder
ivWithin 𝕜 f s x (m …
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_vcomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 2 g t (f x) (fun _ ↦ derivWithin f s x) +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 2 f s x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp, Fintype.sum_sigma, Fintype.sum_unique,
    OrderedFinpartition.default_eq, Fintype.sum_option]
  have : (Fin.cons 1 (fun _ ↦ 1) : Fin 2 → ℕ) = fun _ ↦ 1 :=
    funext <| Fin.forall_fin_two.mpr ⟨rfl, rfl⟩
  simp [OrderedFinpartition.extendEquiv, OrderedFinpartition.extend,
    OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, ht _ (hst hx),
    OrderedFinpartition.atomic, this]
/-
**iteratedDeriv_vcomp_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_vcomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2
 f x) : iteratedDeriv 2 (g ∘ f) x = iteratedFDeriv 𝕜 2 g (f x) (fun _ => deriv f
 x) + fderiv 𝕜 g (f x) (iteratedDeriv 2 f x)
参数：hg : ContDiffAt 𝕜 2 g (f x)；hf : ContDiffAt 𝕜 2 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iteratedDerivWithin_vcomp_two`：iteratedDerivWithin_vcomp_two (hg : ContD
iffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 
𝕜 t) (hs : UniqueDi…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_vcomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x =
      iteratedFDeriv 𝕜 2 g (f x) (fun _ ↦ deriv f x) + fderiv 𝕜 g (f x) (iteratedDeriv 2 f x) := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_two hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**iteratedDerivWithin_vcomp_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_vcomp_three (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf 
: ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (h
x : x in s) (hst : MapsTo f s t) : iteratedDerivWithin 3 (g ∘ f) s x = iteratedF
DerivWithin 𝕜 3 g t (f x) (fun _ => derivWithin f s x) + iteratedFDerivWithin 𝕜 
2 g t (f x) ![iteratedDerivWithin 2 f s x, derivWithin f s x] + 2 • iteratedFDer
ivWithin 𝕜 2 g t (f x) ![derivWithin f s x, iteratedDerivWithin 2 f s x] + fderi
vWithin 𝕜 g t (f x) (itera
参数：hg : ContDiffWithinAt 𝕜 3 g t (f x)；hf : ContDiffWithinAt 𝕜 3 f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition`：iteratedDerivWithi
n_vcomp_eq_sum_orderedFinpartition (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : C
ontDiffWithinAt 𝕜 n f s x) (ht : UniqueDif…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Fintype.sum_sigma`：∀ {ι : Type u_9} {α : ι → Type u_7} {M : Type u_8} [i
nst : Fintype ι] [inst_1 : (i : ι) → Fintype (α i)]   [inst_2 : AddCommMonoid M]
 (f : S…
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.sum_unique`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Unique ι] (f : ι → M),   ∑ x, f x = f defaul
t
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.update_cons_zero`：update_cons_zero : update (cons x p) 0 z = cons z 
p
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `Fin.cons_update`：cons_update : cons x (update p i y) = update (cons x p)
 i.succ y
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_idem`：update_idem {α} [DecidableEq α] {β : α -> Sort*} {
a : α} (v w : β a) (f : forall a, β a) : update (update f a v) a w = update f a 
w
· 使用定理 `iteratedFDerivWithin_one_apply`：iteratedFDerivWithin_one_apply (h : Uniq
ueDiffWithinAt 𝕜 s x) (m : Fin 1 -> E) : iteratedFDerivWithin 𝕜 1 f s x m = fder
ivWithin 𝕜 f s x (m …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
（共 41 条，此处仅展示前 30 条）
-/
theorem iteratedDerivWithin_vcomp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 3 g t (f x) (fun _ ↦ derivWithin f s x) +
      iteratedFDerivWithin 𝕜 2 g t (f x) ![iteratedDerivWithin 2 f s x, derivWithin f s x] +
      2 • iteratedFDerivWithin 𝕜 2 g t (f x) ![derivWithin f s x, iteratedDerivWithin 2 f s x] +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 3 f s x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    OrderedFinpartition.extendMiddle_length, OrderedFinpartition.default_eq, Fintype.sum_unique,
    OrderedFinpartition.atomic_length, OrderedFinpartition.extendLeft_length, Fin.sum_univ_two]
  simp? [add_assoc, two_smul, iteratedFDerivWithin_one_apply (ht _ <| hst hx)] says
    simp only [OrderedFinpartition.extendLeft_partSize, OrderedFinpartition.extendLeft_length,
      OrderedFinpartition.atomic_length, Nat.reduceAdd, OrderedFinpartition.atomic_partSize,
      Fin.isValue, OrderedFinpartition.extendMiddle_partSize, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_one, Fin.default_eq_zero, OrderedFinpartition.extendMiddle_length, Fin.cons_update,
      Fin.succ_zero_eq_one, update_self, update_idem,
      iteratedFDerivWithin_one_apply (ht _ <| hst hx), add_assoc, two_smul]
  have (j : _) : (Fin.cons 1 (Fin.cons 1 fun _ ↦ 1) : Fin 3 → ℕ) j = 1 := by
    fin_cases j <;> rfl
  congr <;> ext x <;> fin_cases x <;> simp [this]
/-
**iteratedDeriv_vcomp_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_vcomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜
 3 f x) : iteratedDeriv 3 (g ∘ f) x = iteratedFDeriv 𝕜 3 g (f x) (fun _ => deriv
 f x) + iteratedFDeriv 𝕜 2 g (f x) ![iteratedDeriv 2 f x, deriv f x] + 2 • itera
tedFDeriv 𝕜 2 g (f x) ![deriv f x, iteratedDeriv 2 f x] + fderiv 𝕜 g (f x) (iter
atedDeriv 3 f x)
参数：hg : ContDiffAt 𝕜 3 g (f x)；hf : ContDiffAt 𝕜 3 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedDerivWithin_vcomp_three`：iteratedDerivWithin_vcomp_three (hg : C
ontDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDif
fOn 𝕜 t) (hs : Unique…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_vcomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      iteratedFDeriv 𝕜 3 g (f x) (fun _ ↦ deriv f x) +
      iteratedFDeriv 𝕜 2 g (f x) ![iteratedDeriv 2 f x, deriv f x] +
      2 • iteratedFDeriv 𝕜 2 g (f x) ![deriv f x, iteratedDeriv 2 f x] +
      fderiv 𝕜 g (f x) (iteratedDeriv 3 f x) := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_three hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

end vcomp

section scomp

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {f : 𝕜 → 𝕜} {s : Set 𝕜} {t : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {i : ℕ}

/-
**iteratedDerivWithin_scomp_eq_sum_orderedFinpartition** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：iteratedDerivWithin_scomp_eq_sum_orderedFinpartition (hg : ContDiffWithinA
t 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs :
 UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) (hi : i <= n) : iteratedDe
rivWithin i (g ∘ f) s x = ∑ c : OrderedFinpartition i, (∏ j, iteratedDerivWithin
 (c.partSize j) f s x) • iteratedDerivWithin c.length g t (f x)
参数：hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition`：iteratedDerivWithi
n_vcomp_eq_sum_orderedFinpartition (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : C
ontDiffWithinAt 𝕜 n f s x) (ht : UniqueDif…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod`：iteratedFDer
ivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n -> 𝕜} : (iteratedFDeri
vWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) m = (∏ i,…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDerivWithin (c.partSize j) f s x) •
          iteratedDerivWithin c.length g t (f x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
/-
**iteratedDeriv_scomp_eq_sum_orderedFinpartition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_scomp_eq_sum_orderedFinpartition (hg : ContDiffAt 𝕜 n g (f x
)) (hf : ContDiffAt 𝕜 n f x) (hi : i <= n) : iteratedDeriv i (g ∘ f) x = ∑ c : O
rderedFinpartition i, (∏ j, iteratedDeriv (c.partSize j) f x) • iteratedDeriv c.
length g (f x)
参数：hg : ContDiffAt 𝕜 n g (f x)；hf : ContDiffAt 𝕜 n f x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_vcomp_eq_sum_orderedFinpartition`：iteratedDeriv_vcomp_eq_s
um_orderedFinpartition (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (
hi : i <= n) : iteratedDeriv i (g ∘ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`：iteratedFDeriv_apply_eq_
iteratedDeriv_mul_prod {m : Fin n -> 𝕜} : (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜)
 -> F) m = (∏ i, m i) • iteratedDeri…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j) f x) • iteratedDeriv c.length g (f x) := by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
/-
**iteratedDerivWithin_scomp_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_scomp_two (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : 
ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx 
: x in s) (hst : MapsTo f s t) : iteratedDerivWithin 2 (g ∘ f) s x = derivWithin
 f s x ^ 2 • iteratedDerivWithin 2 g t (f x) + iteratedDerivWithin 2 f s x • der
ivWithin g t (f x)
参数：hg : ContDiffWithinAt 𝕜 2 g t (f x)；hf : ContDiffWithinAt 𝕜 2 f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_vcomp_two`：iteratedDerivWithin_vcomp_two (hg : ContD
iffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 
𝕜 t) (hs : UniqueDi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod`：iteratedFDer
ivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n -> 𝕜} : (iteratedFDeri
vWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) m = (∏ i,…
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_scomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      derivWithin f s x ^ 2 • iteratedDerivWithin 2 g t (f x) +
      iteratedDerivWithin 2 f s x • derivWithin g t (f x) := by
  rw [iteratedDerivWithin_vcomp_two hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
/-
**iteratedDeriv_scomp_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_scomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2
 f x) : iteratedDeriv 2 (g ∘ f) x = deriv f x ^ 2 • iteratedDeriv 2 g (f x) + it
eratedDeriv 2 f x • deriv g (f x)
参数：hg : ContDiffAt 𝕜 2 g (f x)；hf : ContDiffAt 𝕜 2 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedDerivWithin_scomp_two`：iteratedDerivWithin_scomp_two (hg : ContD
iffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 
𝕜 t) (hs : UniqueDi…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_scomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x
      = deriv f x ^ 2 • iteratedDeriv 2 g (f x) + iteratedDeriv 2 f x • deriv g (f x) := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)
/-
**iteratedDerivWithin_scomp_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_scomp_three (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf 
: ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (h
x : x in s) (hst : MapsTo f s t) : iteratedDerivWithin 3 (g ∘ f) s x = derivWith
in f s x ^ 3 • iteratedDerivWithin 3 g t (f x) + 3 • iteratedDerivWithin 2 f s x
 • derivWithin f s x • iteratedDerivWithin 2 g t (f x) + iteratedDerivWithin 3 f
 s x • derivWithin g t (f x)
参数：hg : ContDiffWithinAt 𝕜 3 g t (f x)；hf : ContDiffWithinAt 𝕜 3 f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_vcomp_three`：iteratedDerivWithin_vcomp_three (hg : C
ontDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDif
fOn 𝕜 t) (hs : Unique…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod`：iteratedFDer
ivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n -> 𝕜} : (iteratedFDeri
vWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) m = (∏ i,…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `_private.Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno.0.iteratedDe
rivWithin_scomp_three._abel_1_2`：∀ {𝕜 : Type u_2} {E : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {g : 𝕜 → E} …
-/
theorem iteratedDerivWithin_scomp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      derivWithin f s x ^ 3 • iteratedDerivWithin 3 g t (f x) +
      3 • iteratedDerivWithin 2 f s x • derivWithin f s x • iteratedDerivWithin 2 g t (f x) +
      iteratedDerivWithin 3 f s x • derivWithin g t (f x) := by
  rw [iteratedDerivWithin_vcomp_three hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, mul_smul, smul_comm (iteratedDerivWithin 2 f s x),
        iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
  abel
/-
**iteratedDeriv_scomp_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_scomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜
 3 f x) : iteratedDeriv 3 (g ∘ f) x = deriv f x ^ 3 • iteratedDeriv 3 g (f x) + 
3 • iteratedDeriv 2 f x • deriv f x • iteratedDeriv 2 g (f x) + iteratedDeriv 3 
f x • deriv g (f x)
参数：hg : ContDiffAt 𝕜 3 g (f x)；hf : ContDiffAt 𝕜 3 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedDerivWithin_scomp_three`：iteratedDerivWithin_scomp_three (hg : C
ontDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDif
fOn 𝕜 t) (hs : Unique…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_scomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      deriv f x ^ 3 • iteratedDeriv 3 g (f x) +
      3 • iteratedDeriv 2 f x • deriv f x • iteratedDeriv 2 g (f x) +
      iteratedDeriv 3 f x • deriv g (f x) := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

end scomp

section comp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {g f : 𝕜 → 𝕜} {s t : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {i : ℕ}

/-
**iteratedDerivWithin_comp_eq_sum_orderedFinpartition** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：iteratedDerivWithin_comp_eq_sum_orderedFinpartition (hg : ContDiffWithinAt
 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs : 
UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) (hi : i <= n) : iteratedDer
ivWithin i (g ∘ f) s x = ∑ c : OrderedFinpartition i, iteratedDerivWithin c.leng
th g t (f x) * ∏ j, iteratedDerivWithin (c.partSize j) f s x
参数：hg : ContDiffWithinAt 𝕜 n g t (f x)；hf : ContDiffWithinAt 𝕜 n f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_scomp_eq_sum_orderedFinpartition`：iteratedDerivWithi
n_scomp_eq_sum_orderedFinpartition (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : C
ontDiffWithinAt 𝕜 n f s x) (ht : UniqueDif…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_comp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i,
        iteratedDerivWithin c.length g t (f x) * ∏ j, iteratedDerivWithin (c.partSize j) f s x := by
  rw [iteratedDerivWithin_scomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [smul_eq_mul, mul_comm]
/-
**iteratedDeriv_comp_eq_sum_orderedFinpartition** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_eq_sum_orderedFinpartition (hg : ContDiffAt 𝕜 n g (f x)
) (hf : ContDiffAt 𝕜 n f x) (hi : i <= n) : iteratedDeriv i (g ∘ f) x = ∑ c : Or
deredFinpartition i, iteratedDeriv c.length g (f x) * ∏ j, iteratedDeriv (c.part
Size j) f x
参数：hg : ContDiffAt 𝕜 n g (f x)；hf : ContDiffAt 𝕜 n f x；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_scomp_eq_sum_orderedFinpartition`：iteratedDeriv_scomp_eq_s
um_orderedFinpartition (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (
hi : i <= n) : iteratedDeriv i (g ∘ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_comp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        iteratedDeriv c.length g (f x) * ∏ j, iteratedDeriv (c.partSize j) f x := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [smul_eq_mul, mul_comm]
/-
**iteratedDerivWithin_comp_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_two (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : C
ontDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx :
 x in s) (hst : MapsTo f s t) : iteratedDerivWithin 2 (g ∘ f) s x = iteratedDeri
vWithin 2 g t (f x) * derivWithin f s x ^ 2 + derivWithin g t (f x) * iteratedDe
rivWithin 2 f s x
参数：hg : ContDiffWithinAt 𝕜 2 g t (f x)；hf : ContDiffWithinAt 𝕜 2 f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_scomp_two`：iteratedDerivWithin_scomp_two (hg : ContD
iffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 
𝕜 t) (hs : UniqueDi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_comp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedDerivWithin 2 g t (f x) * derivWithin f s x ^ 2 +
      derivWithin g t (f x) * iteratedDerivWithin 2 f s x := by
  rw [iteratedDerivWithin_scomp_two hg hf ht hs hx hst]
  simp only [smul_eq_mul, mul_comm]
/-
**iteratedDeriv_comp_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 
f x) : iteratedDeriv 2 (g ∘ f) x = iteratedDeriv 2 g (f x) * deriv f x ^ 2 + der
iv g (f x) * iteratedDeriv 2 f x
参数：hg : ContDiffAt 𝕜 2 g (f x)；hf : ContDiffAt 𝕜 2 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedDerivWithin_comp_two`：iteratedDerivWithin_comp_two (hg : ContDif
fWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x) (ht : UniqueDiffOn 𝕜 
t) (hs : UniqueDif…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_comp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x =
      iteratedDeriv 2 g (f x) * deriv f x ^ 2 + deriv g (f x) * iteratedDeriv 2 f x := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)
/-
**iteratedDerivWithin_comp_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_comp_three (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf :
 ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx
 : x in s) (hst : MapsTo f s t) : iteratedDerivWithin 3 (g ∘ f) s x = iteratedDe
rivWithin 3 g t (f x) * derivWithin f s x ^ 3 + 3 * iteratedDerivWithin 2 g t (f
 x) * iteratedDerivWithin 2 f s x * derivWithin f s x + derivWithin g t (f x) * 
iteratedDerivWithin 3 f s x
参数：hg : ContDiffWithinAt 𝕜 3 g t (f x)；hf : ContDiffWithinAt 𝕜 3 f s x；ht : Uniq
ueDiffOn 𝕜 t；hs : UniqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_scomp_three`：iteratedDerivWithin_scomp_three (hg : C
ontDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDif
fOn 𝕜 t) (hs : Unique…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 33 条，此处仅展示前 30 条）
-/
theorem iteratedDerivWithin_comp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      iteratedDerivWithin 3 g t (f x) * derivWithin f s x ^ 3 +
      3 * iteratedDerivWithin 2 g t (f x) * iteratedDerivWithin 2 f s x * derivWithin f s x +
      derivWithin g t (f x) * iteratedDerivWithin 3 f s x := by
  rw [iteratedDerivWithin_scomp_three hg hf ht hs hx hst]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring
/-
**iteratedDeriv_comp_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_comp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 
3 f x) : iteratedDeriv 3 (g ∘ f) x = iteratedDeriv 3 g (f x) * deriv f x ^ 3 + 3
 * iteratedDeriv 2 g (f x) * iteratedDeriv 2 f x * deriv f x + deriv g (f x) * i
teratedDeriv 3 f x
参数：hg : ContDiffAt 𝕜 3 g (f x)；hf : ContDiffAt 𝕜 3 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iteratedDerivWithin_comp_three`：iteratedDerivWithin_comp_three (hg : Con
tDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x) (ht : UniqueDiffO
n 𝕜 t) (hs : UniqueD…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem iteratedDeriv_comp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      iteratedDeriv 3 g (f x) * deriv f x ^ 3 +
      3 * iteratedDeriv 2 g (f x) * iteratedDeriv 2 f x * deriv f x +
      deriv g (f x) * iteratedDeriv 3 f x := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

end comp

