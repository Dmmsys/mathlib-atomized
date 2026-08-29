/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Bilipschitz
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Constructions of Hilbert C⋆-modules

In this file we define the following constructions of `CStarModule`s where `A` denotes a C⋆-algebra.
For some of the types listed below, the instance is declared on the type synonym `WithCStarModule E`
(with the notation `C⋆ᵐᵒᵈ E`), instead of on `E` itself; we explain the reasoning behind each
decision below.

1. `A` as a `CStarModule` over itself.
2. `C⋆ᵐᵒᵈ(A, E × F)` as a `CStarModule` over `A`, when `E` and `F` are themselves `CStarModule`s
  over `A`.
3. `C⋆ᵐᵒᵈ (A, Π i : ι, E i)` as a `CStarModule` over `A`, when each `E i` is a `CStarModule` over
  `A` and `ι` is a `Fintype`.
4. `E` as a `CStarModule` over `ℂ`, when `E` is an `InnerProductSpace` over `ℂ`.

For `E × F` and `Π i : ι, E i`, we are required to declare the instance on a type synonym rather
than on the product or pi-type itself because the existing norm on these types does not agree with
the one induced by the C⋆-module structure. Moreover, the norm induced by the C⋆-module structure
doesn't agree with any other natural norm on these types (e.g., `WithLp 2 (E × F)` unless `A := ℂ`),
so we need a new synonym.

On `A` (a C⋆-algebra) and `E` (an inner product space), we declare the instances on the types
themselves to ease the use of the C⋆-module structure. This does have the potential to cause
inconvenience (as sometimes Lean will see terms of type `A` and apply lemmas pertaining to
C⋆-modules to those terms, when the lemmas were actually intended for terms of some other
C⋆-module in context, say `F`, in which case the arguments must be provided explicitly; see for
instance the application of `CStarModule.norm_eq_sqrt_norm_inner_self` in the proof of
`WithCStarModule.max_le_prod_norm` below). However, we believe that this, hopefully rare,
inconvenience is outweighed by avoiding translating between type synonyms where possible.

For more details on the importance of the `WithCStarModule` type synonym, see the module
documentation for `Analysis.CStarAlgebra.Module.Synonym`.

## Implementation notes

When `A := ℂ` and `E := ℂ`, then `ℂ` is both a C⋆-algebra (so it inherits a `CStarModule` instance
via (1) above) and an inner product space (so it inherits a `CStarModule` instance via (4) above).
We provide a sanity check ensuring that these two instances are definitionally equal. We also ensure
that the `Inner ℂ ℂ` instance from `InnerProductSpace` is definitionally equal to the one inherited
from the `CStarModule` instances.

Note that `C⋆ᵐᵒᵈ(A, E)` is *already* equipped with a bornology and uniformity whenever `E` is
(namely, the pullback of the respective structures through `WithCStarModule.equiv`), so in each of
the above cases, it is necessary to temporarily instantiate `C⋆ᵐᵒᵈ(A, E)` with
`CStarModule.normedAddCommGroup`, show the resulting type is bilipschitz equivalent to `E` via
`WithCStarModule.equiv` (in the first and last case, this map is actually trivially an isometry),
and then replace the uniformity and bornology with the correct ones.

-/

@[expose] public section

open CStarModule CStarRing

namespace WithCStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-! ## A C⋆-algebra as a C⋆-module over itself -/

section Self

variable [StarOrderedRing A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CStarModule A A
  body: y * star x
  inner_add_right := add_mul ..
  inner_self_nonneg := mul_star_self_nonneg _
  inner_self := CStarRing.mul_star_self_eq_zero_iff _
  inner_op_smul_right := mul_assoc ..
  inner_smul_right_complex := smul_mul_assoc ..
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
simpa [sq] using Eq.symm CStarRing.norm_self_mul_star

中文:
实例 :
  签名: CStar模 A A
  定义体: y * star x
  inner_add_right := add_mul ..
  inner_self_nonneg := mul_star_self_nonneg _
  inner_self := CStarRing.mul_star_self_eq_zero_iff _
  inner_op_smul_right := mul_assoc ..
  inner_smul_right_complex := smul_mul_assoc ..
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
simpa [sq] using Eq.symm CStarRing.norm_self_mul_star
-/
instance : CStarModule A A where
  inner x y := y * star x
  inner_add_right := add_mul ..
  inner_self_nonneg := mul_star_self_nonneg _
  inner_self := CStarRing.mul_star_self_eq_zero_iff _
  inner_op_smul_right := mul_assoc ..
  inner_smul_right_complex := smul_mul_assoc ..
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
simpa [sq] using Eq.symm CStarRing.norm_self_mul_star

open scoped InnerProductSpace in
/--
lemma `inner_def` / 引理 `inner_def`

English:
lemma inner_def
  given: (x y : A)
  statement: ⟪x, y⟫_A = y * star x
  proof: rfl

中文:
引理 inner_def
  条件: (x y : A)
  结论: ⟪x, y⟫_A = y * star x
  证明: rfl
-/
lemma inner_def (x y : A) : ⟪x, y⟫_A = y * star x := rfl

end Self

/-! ## Products of C⋆-modules -/

section Prod

open scoped InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [Module Complex E] [SMul A E]
variable [NormedAddCommGroup F] [Module Complex F] [SMul A F]
variable [CStarModule A E] [CStarModule A F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Norm C⋆ᵐᵒᵈ(A, E × F)
  body: √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖

中文:
实例 :
  签名: 范数 C⋆ᵐᵒᵈ(A, E × F)
  定义体: √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
-/
noncomputable instance : Norm C⋆ᵐᵒᵈ(A, E × F) where
  norm x := √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖

/--
lemma `prod_norm` / 引理 `prod_norm`

English:
lemma prod_norm
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: ‖x‖ = √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
  proof: rfl

中文:
引理 prod_norm
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: ‖x‖ = √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
  证明: rfl
-/
lemma prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ = √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := rfl

/--
lemma `prod_norm_sq` / 引理 `prod_norm_sq`

English:
lemma prod_norm_sq
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
  proof: by
  simp [prod_norm]

中文:
引理 prod_norm_sq
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
  证明: by
  simp [prod_norm]

Depends on / 依赖: prod_norm
-/
lemma prod_norm_sq (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := by
  simp [prod_norm]

/--
lemma `prod_norm_le_norm_add` / 引理 `prod_norm_le_norm_add`

English:
lemma prod_norm_le_norm_add
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: ‖x‖ <= ‖x.1‖ + ‖x.2‖
  proof: by
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  calc ‖x‖ ^ 2 <= ‖⟪x.1, x.1⟫_A‖ + ‖⟪x.2, x.2⟫_A‖ := prod_norm_sq x ▸ norm_add_le _ _
    _ = ‖x.1‖ ^ 2 + 0 + ‖x.2‖ ^ 2 := by simp [norm_sq_eq A]
    _ <= ‖x.1‖ ^ 2 + 2 * ‖x.1‖ * ‖x.2‖ + ‖x.2‖ ^ 2 := by gcongr; positivity
    _ = (‖x.1‖ + ‖x.2‖) ^ 2 := by ring

中文:
引理 prod_norm_le_norm_add
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: ‖x‖ <= ‖x.1‖ + ‖x.2‖
  证明: by
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  calc ‖x‖ ^ 2 <= ‖⟪x.1, x.1⟫_A‖ + ‖⟪x.2, x.2⟫_A‖ := prod_norm_sq x ▸ norm_add_le _ _
    _ = ‖x.1‖ ^ 2 + 0 + ‖x.2‖ ^ 2 := by simp [norm_sq_eq A]
    _ <= ‖x.1‖ ^ 2 + 2 * ‖x.1‖ * ‖x.2‖ + ‖x.2‖ ^ 2 := by gcongr; positivity
    _ = (‖x.1‖ + ‖x.2‖) ^ 2 := by ring

Depends on / 依赖: abs_le_of_sq_le_sq, norm_add_le, norm_sq_eq, prod_norm_sq
-/
lemma prod_norm_le_norm_add (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ <= ‖x.1‖ + ‖x.2‖ := by
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  calc ‖x‖ ^ 2 <= ‖⟪x.1, x.1⟫_A‖ + ‖⟪x.2, x.2⟫_A‖ := prod_norm_sq x ▸ norm_add_le _ _
    _ = ‖x.1‖ ^ 2 + 0 + ‖x.2‖ ^ 2 := by simp [norm_sq_eq A]
    _ <= ‖x.1‖ ^ 2 + 2 * ‖x.1‖ * ‖x.2‖ + ‖x.2‖ ^ 2 := by gcongr; positivity
    _ = (‖x.1‖ + ‖x.2‖) ^ 2 := by ring

variable [StarOrderedRing A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CStarModule A C⋆ᵐᵒᵈ(A, E × F)
  body: ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A
  inner_add_right {x y z} := by simpa using add_add_add_comm ..
  inner_self_nonneg := add_nonneg CStarModule.inner_self_nonneg CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
.injective apply equiv A (E × F)
    ext
· refine inner_self.mp le_antisymm ?_ (inner_self_nonneg (A := A))
.trans_eq h exact le_add_of_nonneg_right CStarModule.inner_self_nonneg
· refine inner_self.mp le_antisymm ?_ (inner_self_nonneg (A := A))
.trans_eq h exact le_add_of_nonneg_left CStarModule.inner_self_nonneg
  inner_op_smul_right := by simp [mul_add]
  inner_smul_right_complex := by simp [smul_add]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl

中文:
实例 :
  签名: CStar模 A C⋆ᵐᵒᵈ(A, E × F)
  定义体: ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A
  inner_add_right {x y z} := by simpa using add_add_add_comm ..
  inner_self_nonneg := add_nonneg CStarModule.inner_self_nonneg CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
.injective apply equiv A (E × F)
    ext
· refine inner_self.mp le_antisymm ?_ (inner_self_nonneg (A := A))
.trans_eq h exact le_add_of_nonneg_right CStarModule.inner_self_nonneg
· refine inner_self.mp le_antisymm ?_ (inner_self_nonneg (A := A))
.trans_eq h exact le_add_of_nonneg_left CStarModule.inner_self_nonneg
  inner_op_smul_right := by simp [mul_add]
  inner_smul_right_complex := by simp [smul_add]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl
-/
noncomputable instance : CStarModule A C⋆ᵐᵒᵈ(A, E × F) where
  inner x y := ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A
  inner_add_right {x y z} := by simpa using add_add_add_comm ..
  inner_self_nonneg := add_nonneg CStarModule.inner_self_nonneg CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
.injective apply equiv A (E × F)
    ext
· refine inner_self.mp le_antisymm ?_ (inner_self_nonneg (A := A))
.trans_eq h exact le_add_of_nonneg_right CStarModule.inner_self_nonneg
· refine inner_self.mp le_antisymm ?_ (inner_self_nonneg (A := A))
.trans_eq h exact le_add_of_nonneg_left CStarModule.inner_self_nonneg
  inner_op_smul_right := by simp [mul_add]
  inner_smul_right_complex := by simp [smul_add]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl

/--
lemma `prod_inner` / 引理 `prod_inner`

English:
lemma prod_inner
  given: (x y : C⋆ᵐᵒᵈ(A, E × F))
  statement: ⟪x, y⟫_A = ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A
  proof: rfl

中文:
引理 prod_inner
  条件: (x y : C⋆ᵐᵒᵈ(A, E × F))
  结论: ⟪x, y⟫_A = ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A
  证明: rfl
-/
lemma prod_inner (x y : C⋆ᵐᵒᵈ(A, E × F)) : ⟪x, y⟫_A = ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A := rfl

/--
lemma `max_le_prod_norm` / 引理 `max_le_prod_norm`

English:
lemma max_le_prod_norm
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: max ‖x.1‖ ‖x.2‖ <= ‖x‖
  proof: by
  rw [prod_norm]
  simp only [norm_eq_sqrt_norm_inner_self (A := A) (E := E),
    norm_eq_sqrt_norm_inner_self (A := A) (E := F), max_le_iff, norm_nonneg,
    Real.sqrt_le_sqrt_iff]
  constructor
  all_goals
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (A := A) ?_ ?_
    all_goals
      aesop (add safe apply CStarModule.inner_self_nonneg)

中文:
引理 max_le_prod_norm
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: 最大值 ‖x.1‖ ‖x.2‖ <= ‖x‖
  证明: by
  rw [prod_norm]
  simp only [norm_eq_sqrt_norm_inner_self (A := A) (E := E),
    norm_eq_sqrt_norm_inner_self (A := A) (E := F), max_le_iff, norm_nonneg,
    Real.sqrt_le_sqrt_iff]
  constructor
  all_goals
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (A := A) ?_ ?_
    all_goals
      aesop (add safe apply CStarModule.inner_self_nonneg)

Depends on / 依赖: CStarAlgebra, CStarAlgebra.norm_le_norm_of_nonneg_of_le, CStarModule, CStarModule.inner_self_nonneg, Real.sqrt_le_sqrt_iff, all_goals, inner_self_nonneg, max_le_iff, norm_eq_sqrt_norm_inner_self, norm_le_norm_of_nonneg_of_le, norm_nonneg, prod_norm, sqrt_le_sqrt_iff
-/
lemma max_le_prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : max ‖x.1‖ ‖x.2‖ <= ‖x‖ := by
  rw [prod_norm]
  simp only [norm_eq_sqrt_norm_inner_self (A := A) (E := E),
    norm_eq_sqrt_norm_inner_self (A := A) (E := F), max_le_iff, norm_nonneg,
    Real.sqrt_le_sqrt_iff]
  constructor
  all_goals
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (A := A) ?_ ?_
    all_goals
      aesop (add safe apply CStarModule.inner_self_nonneg)

/--
lemma `norm_equiv_le_norm_prod` / 引理 `norm_equiv_le_norm_prod`

English:
lemma norm_equiv_le_norm_prod
  given: (x : C⋆ᵐᵒᵈ(A, E × F))
  statement: ‖equiv A (E × F) x‖ <= ‖x‖
  proof: max_le_prod_norm x

中文:
引理 norm_equiv_le_norm_prod
  条件: (x : C⋆ᵐᵒᵈ(A, E × F))
  结论: ‖equiv A (E × F) x‖ <= ‖x‖
  证明: max_le_prod_norm x

Depends on / 依赖: max_le_prod_norm
-/
lemma norm_equiv_le_norm_prod (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖equiv A (E × F) x‖ <= ‖x‖ :=
  max_le_prod_norm x

section Aux

-- We temporarily disable the uniform space and bornology on `C⋆ᵐᵒᵈ A` while proving
-- that those induced by the new norm are equal to the old ones.
attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology

/-- A normed additive commutative group structure on `C⋆ᵐᵒᵈ(A, E × F)` with the wrong topology,
uniformity and bornology. This is only used to build the instance with the correct forgetful
inheritance data. -/
@[instance_reducible]
/--
Definition of `normedAddCommGroupProdAux` / `normedAddCommGroupProdAux` 的定义

English:
definition normedAddCommGroupProdAux
  signature: : NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F)
  body: NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

中文:
定义 normedAddCommGroupProdAux
  签名: : 赋范交换加群 C⋆ᵐᵒᵈ(A, E × F)
  定义体: NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

Depends on / 依赖: CStarModule, CStarModule.normedSpaceCore, NormedAddCommGroup, NormedAddCommGroup.ofCore, normedSpaceCore, ofCore
-/
noncomputable def normedAddCommGroupProdAux : NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

attribute [local instance] normedAddCommGroupProdAux

open Filter Uniformity Bornology

/--
lemma `antilipschitzWith_two_equiv_prod_aux` / 引理 `antilipschitzWith_two_equiv_prod_aux`

English:
lemma antilipschitzWith_two_equiv_prod_aux
  statement: AntilipschitzWith 2 (equiv A (E × F))
  proof: AddMonoidHomClass.antilipschitz_of_bound (linearEquiv Complex A (E × F)) fun x => by
.trans apply prod_norm_le_norm_add x
    simp only [NNReal.coe_ofNat, linearEquiv_apply, two_mul]
    gcongr
    · exact norm_fst_le x
    · exact norm_snd_le x

中文:
引理 antilipschitzWith_two_equiv_prod_aux
  结论: AntilipschitzWith 2 (equiv A (E × F))
  证明: AddMonoidHomClass.antilipschitz_of_bound (linearEquiv Complex A (E × F)) fun x => by
.trans apply prod_norm_le_norm_add x
    simp only [NNReal.coe_ofNat, linearEquiv_apply, two_mul]
    gcongr
    · exact norm_fst_le x
    · exact norm_snd_le x
-/
private lemma antilipschitzWith_two_equiv_prod_aux : AntilipschitzWith 2 (equiv A (E × F)) :=
  AddMonoidHomClass.antilipschitz_of_bound (linearEquiv Complex A (E × F)) fun x => by
.trans apply prod_norm_le_norm_add x
    simp only [NNReal.coe_ofNat, linearEquiv_apply, two_mul]
    gcongr
    · exact norm_fst_le x
    · exact norm_snd_le x

/--
lemma `lipschitzWith_one_equiv_prod_aux` / 引理 `lipschitzWith_one_equiv_prod_aux`

English:
lemma lipschitzWith_one_equiv_prod_aux
  statement: LipschitzWith 1 (equiv A (E × F))
  proof: AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv Complex A (E × F)) 1 by
    simpa using! norm_equiv_le_norm_prod

中文:
引理 lipschitzWith_one_equiv_prod_aux
  结论: LipschitzWith 1 (equiv A (E × F))
  证明: AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv Complex A (E × F)) 1 by
    simpa using! norm_equiv_le_norm_prod
-/
private lemma lipschitzWith_one_equiv_prod_aux : LipschitzWith 1 (equiv A (E × F)) :=
AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv Complex A (E × F)) 1 by
    simpa using! norm_equiv_le_norm_prod

/--
lemma `uniformity_prod_eq_aux` / 引理 `uniformity_prod_eq_aux`

English:
lemma uniformity_prod_eq_aux
  proof: uniformity_eq_of_bilipschitz antilipschitzWith_two_equiv_prod_aux lipschitzWith_one_equiv_prod_aux

中文:
引理 uniformity_prod_eq_aux
  证明: uniformity_eq_of_bilipschitz antilipschitzWith_two_equiv_prod_aux lipschitzWith_one_equiv_prod_aux
-/
private lemma uniformity_prod_eq_aux :
    𝓤[(inferInstance : UniformSpace (E × F)).comap <| equiv _ _] = 𝓤 C⋆ᵐᵒᵈ(A, E × F) :=
  uniformity_eq_of_bilipschitz antilipschitzWith_two_equiv_prod_aux lipschitzWith_one_equiv_prod_aux

/--
lemma `isBounded_prod_iff_aux` / 引理 `isBounded_prod_iff_aux`

English:
lemma isBounded_prod_iff_aux
  given: (s : Set C⋆ᵐᵒᵈ(A, E × F))
  proof: isBounded_iff_of_bilipschitz antilipschitzWith_two_equiv_prod_aux
    lipschitzWith_one_equiv_prod_aux s

中文:
引理 isBounded_prod_iff_aux
  条件: (s : 集合 C⋆ᵐᵒᵈ(A, E × F))
  证明: isBounded_iff_of_bilipschitz antilipschitzWith_two_equiv_prod_aux
    lipschitzWith_one_equiv_prod_aux s
-/
private lemma isBounded_prod_iff_aux (s : Set C⋆ᵐᵒᵈ(A, E × F)) :
    @IsBounded _ (induced <| equiv A (E × F)) s ↔ IsBounded s :=
  isBounded_iff_of_bilipschitz antilipschitzWith_two_equiv_prod_aux
    lipschitzWith_one_equiv_prod_aux s

end Aux

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F)
  body: fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_

中文:
实例 :
  签名: 赋范交换加群 C⋆ᵐᵒᵈ(A, E × F)
  定义体: fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_

Depends on / 依赖: fast_instance, normedSpaceCore, ofCoreReplaceAll
-/
noncomputable instance : NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F) :=
  fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_
where finally
  exacts [uniformity_prod_eq_aux, isBounded_prod_iff_aux]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedSpace Complex C⋆ᵐᵒᵈ(A, E × F)
  body: .ofCore (normedSpaceCore A)

中文:
实例 :
  签名: 赋范空间 复形 C⋆ᵐᵒᵈ(A, E × F)
  定义体: .ofCore (normedSpaceCore A)

Depends on / 依赖: normedSpaceCore, ofCore
-/
noncomputable instance : NormedSpace Complex C⋆ᵐᵒᵈ(A, E × F) := .ofCore (normedSpaceCore A)

end Prod

/-! ## Pi-types of C⋆-modules -/

section Pi

open scoped InnerProductSpace

variable {ι : Type*} {E : ι -> Type*} [Fintype ι]
variable [forall i, NormedAddCommGroup (E i)] [forall i, Module Complex (E i)] [forall i, SMul A (E i)]
variable [forall i, CStarModule A (E i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Norm C⋆ᵐᵒᵈ(A, Π i, E i)
  body: √‖∑ i, ⟪x i, x i⟫_A‖

中文:
实例 :
  签名: 范数 C⋆ᵐᵒᵈ(A, Π i, E i)
  定义体: √‖∑ i, ⟪x i, x i⟫_A‖
-/
noncomputable instance : Norm C⋆ᵐᵒᵈ(A, Π i, E i) where
  norm x := √‖∑ i, ⟪x i, x i⟫_A‖

/--
lemma `pi_norm` / 引理 `pi_norm`

English:
lemma pi_norm
  given: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  statement: ‖x‖ = √‖∑ i, ⟪x i, x i⟫_A‖
  proof: by
  with_reducible_and_instances rfl

中文:
引理 pi_norm
  条件: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  结论: ‖x‖ = √‖∑ i, ⟪x i, x i⟫_A‖
  证明: by
  with_reducible_and_instances rfl

Depends on / 依赖: with_reducible_and_instances
-/
lemma pi_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ = √‖∑ i, ⟪x i, x i⟫_A‖ := by
  with_reducible_and_instances rfl

/--
lemma `pi_norm_sq` / 引理 `pi_norm_sq`

English:
lemma pi_norm_sq
  given: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  statement: ‖x‖ ^ 2 = ‖∑ i, ⟪x i, x i⟫_A‖
  proof: by
  simp [pi_norm]

中文:
引理 pi_norm_sq
  条件: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  结论: ‖x‖ ^ 2 = ‖∑ i, ⟪x i, x i⟫_A‖
  证明: by
  simp [pi_norm]

Depends on / 依赖: pi_norm
-/
lemma pi_norm_sq (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ ^ 2 = ‖∑ i, ⟪x i, x i⟫_A‖ := by
  simp [pi_norm]

open Finset in
/--
lemma `pi_norm_le_sum_norm` / 引理 `pi_norm_le_sum_norm`

English:
lemma pi_norm_le_sum_norm
  given: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  statement: ‖x‖ <= ∑ i, ‖x i‖
  proof: by
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  calc ‖x‖ ^ 2 <= ∑ i, ‖⟪x i, x i⟫_A‖ := pi_norm_sq x ▸ norm_sum_le _ _
    _ = ∑ i, ‖x i‖ ^ 2 := by simp only [norm_sq_eq A]
    _ <= (∑ i, ‖x i‖) ^ 2 := sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

中文:
引理 pi_norm_le_sum_norm
  条件: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  结论: ‖x‖ <= ∑ i, ‖x i‖
  证明: by
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  calc ‖x‖ ^ 2 <= ∑ i, ‖⟪x i, x i⟫_A‖ := pi_norm_sq x ▸ norm_sum_le _ _
    _ = ∑ i, ‖x i‖ ^ 2 := by simp only [norm_sq_eq A]
    _ <= (∑ i, ‖x i‖) ^ 2 := sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

Depends on / 依赖: abs_le_of_sq_le_sq, norm_nonneg, norm_sq_eq, norm_sum_le, pi_norm_sq, sum_sq_le_sq_sum_of_nonneg
-/
lemma pi_norm_le_sum_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ <= ∑ i, ‖x i‖ := by
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  calc ‖x‖ ^ 2 <= ∑ i, ‖⟪x i, x i⟫_A‖ := pi_norm_sq x ▸ norm_sum_le _ _
    _ = ∑ i, ‖x i‖ ^ 2 := by simp only [norm_sq_eq A]
    _ <= (∑ i, ‖x i‖) ^ 2 := sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

variable [StarOrderedRing A]

open Finset in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CStarModule A C⋆ᵐᵒᵈ(A, Π i, E i)
  body: ∑ i, ⟪x i, y i⟫_A
  inner_add_right {x y z} := by simp [sum_add_distrib]
inner_self_nonneg := sum_nonneg fun _ _ => CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
    ext i
refine inner_self.mp le_antisymm (le_of_le_of_eq ?_ h) inner_self_nonneg
    exact single_le_sum (fun i _ => CStarModule.inner_self_nonneg (A := A) (x := x i)) (mem_univ _)
  inner_op_smul_right := by simp [mul_sum]
  inner_smul_right_complex := by simp [smul_sum]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl

中文:
实例 :
  签名: CStar模 A C⋆ᵐᵒᵈ(A, Π i, E i)
  定义体: ∑ i, ⟪x i, y i⟫_A
  inner_add_right {x y z} := by simp [sum_add_distrib]
inner_self_nonneg := sum_nonneg fun _ _ => CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
    ext i
refine inner_self.mp le_antisymm (le_of_le_of_eq ?_ h) inner_self_nonneg
    exact single_le_sum (fun i _ => CStarModule.inner_self_nonneg (A := A) (x := x i)) (mem_univ _)
  inner_op_smul_right := by simp [mul_sum]
  inner_smul_right_complex := by simp [smul_sum]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl
-/
noncomputable instance : CStarModule A C⋆ᵐᵒᵈ(A, Π i, E i) where
  inner x y := ∑ i, ⟪x i, y i⟫_A
  inner_add_right {x y z} := by simp [sum_add_distrib]
inner_self_nonneg := sum_nonneg fun _ _ => CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
    ext i
refine inner_self.mp le_antisymm (le_of_le_of_eq ?_ h) inner_self_nonneg
    exact single_le_sum (fun i _ => CStarModule.inner_self_nonneg (A := A) (x := x i)) (mem_univ _)
  inner_op_smul_right := by simp [mul_sum]
  inner_smul_right_complex := by simp [smul_sum]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl

/--
lemma `pi_inner` / 引理 `pi_inner`

English:
lemma pi_inner
  given: (x y : C⋆ᵐᵒᵈ(A, Π i, E i))
  statement: ⟪x, y⟫_A = ∑ i, ⟪x i, y i⟫_A
  proof: rfl

@[simp]

中文:
引理 pi_inner
  条件: (x y : C⋆ᵐᵒᵈ(A, Π i, E i))
  结论: ⟪x, y⟫_A = ∑ i, ⟪x i, y i⟫_A
  证明: rfl

@[simp]
-/
lemma pi_inner (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) : ⟪x, y⟫_A = ∑ i, ⟪x i, y i⟫_A := rfl

@[simp]
/--
lemma `inner_single_left` / 引理 `inner_single_left`

English:
lemma inner_single_left
  given: [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i)
  proof: by ⟪equiv _ _
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]

中文:
引理 inner_single_left
  条件: [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i)
  证明: by ⟪equiv _ _
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_single, all_goals, equiv_symm_pi_apply, pi_inner, sum_eq_single
-/
lemma inner_single_left [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i) :
.symm Pi.single i y, x⟫_A = ⟪y, x i⟫_A := by ⟪equiv _ _
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]
/--
lemma `inner_single_right` / 引理 `inner_single_right`

English:
lemma inner_single_right
  given: [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i)
  proof: by ⟪x, equiv _ _
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]

中文:
引理 inner_single_right
  条件: [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i)
  证明: by ⟪x, equiv _ _
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]

Depends on / 依赖: Finset, Finset.sum_eq_single, all_goals, equiv_symm_pi_apply, pi_inner, sum_eq_single
-/
lemma inner_single_right [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i) :
.symm Pi.single i y⟫_A = ⟪x i, y⟫_A := by ⟪x, equiv _ _
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]
/--
lemma `norm_single` / 引理 `norm_single`

English:
lemma norm_single
  given: [DecidableEq ι] (i : ι) (y : E i)
  proof: by ‖equiv A _
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp [norm_sq_eq A]

中文:
引理 norm_single
  条件: [DecidableEq ι] (i : ι) (y : E i)
  证明: by ‖equiv A _
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp [norm_sq_eq A]

Depends on / 依赖: NormedAddCommGroup, norm_sq_eq, normedAddCommGroup
-/
lemma norm_single [DecidableEq ι] (i : ι) (y : E i) :
.symm Pi.single i y‖ = ‖y‖ := by ‖equiv A _
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp [norm_sq_eq A]

/--
lemma `norm_apply_le_norm` / 引理 `norm_apply_le_norm`

English:
lemma norm_apply_le_norm
  given: (x : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι)
  statement: ‖x i‖ <= ‖x‖
  proof: by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  rw [pi_norm_sq]; rw [norm_sq_eq A]
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg ?_
  exact Finset.single_le_sum (fun j _ => inner_self_nonneg (A := A) (x := x j)) (Finset.mem_univ i)

中文:
引理 norm_apply_le_norm
  条件: (x : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι)
  结论: ‖x i‖ <= ‖x‖
  证明: by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  rw [pi_norm_sq]; rw [norm_sq_eq A]
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg ?_
  exact Finset.single_le_sum (fun j _ => inner_self_nonneg (A := A) (x := x j)) (Finset.mem_univ i)

Depends on / 依赖: CStarAlgebra, CStarAlgebra.norm_le_norm_of_nonneg_of_le, Finset, Finset.mem_univ, Finset.single_le_sum, NormedAddCommGroup, abs_le_of_sq_le_sq, inner_self_nonneg, mem_univ, norm_le_norm_of_nonneg_of_le, norm_sq_eq, normedAddCommGroup, pi_norm_sq, single_le_sum
-/
lemma norm_apply_le_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) : ‖x i‖ <= ‖x‖ := by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
.2 refine abs_le_of_sq_le_sq' ?_ (by positivity)
  rw [pi_norm_sq]; rw [norm_sq_eq A]
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg ?_
  exact Finset.single_le_sum (fun j _ => inner_self_nonneg (A := A) (x := x j)) (Finset.mem_univ i)

open Finset in
/--
lemma `norm_equiv_le_norm_pi` / 引理 `norm_equiv_le_norm_pi`

English:
lemma norm_equiv_le_norm_pi
  given: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  statement: ‖equiv _ _ x‖ <= ‖x‖
  proof: by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  simpa using norm_apply_le_norm x

中文:
引理 norm_equiv_le_norm_pi
  条件: (x : C⋆ᵐᵒᵈ(A, Π i, E i))
  结论: ‖equiv _ _ x‖ <= ‖x‖
  证明: by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  simpa using norm_apply_le_norm x

Depends on / 依赖: NormedAddCommGroup, norm_apply_le_norm, normedAddCommGroup, pi_norm_le_iff_of_nonneg
-/
lemma norm_equiv_le_norm_pi (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖equiv _ _ x‖ <= ‖x‖ := by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  simpa using norm_apply_le_norm x

section Aux

-- We temporarily disable the uniform space and bornology on `C⋆ᵐᵒᵈ A` while proving
-- that those induced by the new norm are equal to the old ones.
attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology

/-- A normed additive commutative group structure on `C⋆ᵐᵒᵈ(A, Π i, E i)` with the wrong topology,
uniformity and bornology. This is only used to build the instance with the correct forgetful
inheritance data. -/
@[instance_reducible]
/--
Definition of `normedAddCommGroupPiAux` / `normedAddCommGroupPiAux` 的定义

English:
definition normedAddCommGroupPiAux
  signature: : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i)
  body: NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

中文:
定义 normedAddCommGroupPiAux
  签名: : 赋范交换加群 C⋆ᵐᵒᵈ(A, Π i, E i)
  定义体: NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

Depends on / 依赖: CStarModule, CStarModule.normedSpaceCore, NormedAddCommGroup, NormedAddCommGroup.ofCore, normedSpaceCore, ofCore
-/
noncomputable def normedAddCommGroupPiAux : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

attribute [local instance] normedAddCommGroupPiAux

open Uniformity Bornology

/--
lemma `antilipschitzWith_card_equiv_pi_aux` / 引理 `antilipschitzWith_card_equiv_pi_aux`

English:
lemma antilipschitzWith_card_equiv_pi_aux
  proof: AddMonoidHomClass.antilipschitz_of_bound (linearEquiv Complex A (Π i, E i)) fun x => by
    simp only [NNReal.coe_natCast, linearEquiv_apply]
    calc ‖x‖ <= ∑ i, ‖x i‖ := pi_norm_le_sum_norm x
      _ <= ∑ _, ‖⇑x‖ := Finset.sum_le_sum fun _ _ => norm_le_pi_norm ..
      _ <= Fintype.card ι * ‖⇑x‖ := by simp

中文:
引理 antilipschitzWith_card_equiv_pi_aux
  证明: AddMonoidHomClass.antilipschitz_of_bound (linearEquiv Complex A (Π i, E i)) fun x => by
    simp only [NNReal.coe_natCast, linearEquiv_apply]
    calc ‖x‖ <= ∑ i, ‖x i‖ := pi_norm_le_sum_norm x
      _ <= ∑ _, ‖⇑x‖ := Finset.sum_le_sum fun _ _ => norm_le_pi_norm ..
      _ <= Fintype.card ι * ‖⇑x‖ := by simp
-/
private lemma antilipschitzWith_card_equiv_pi_aux :
    AntilipschitzWith (Fintype.card ι) (equiv A (Π i, E i)) :=
  AddMonoidHomClass.antilipschitz_of_bound (linearEquiv Complex A (Π i, E i)) fun x => by
    simp only [NNReal.coe_natCast, linearEquiv_apply]
    calc ‖x‖ <= ∑ i, ‖x i‖ := pi_norm_le_sum_norm x
      _ <= ∑ _, ‖⇑x‖ := Finset.sum_le_sum fun _ _ => norm_le_pi_norm ..
      _ <= Fintype.card ι * ‖⇑x‖ := by simp

/--
lemma `lipschitzWith_one_equiv_pi_aux` / 引理 `lipschitzWith_one_equiv_pi_aux`

English:
lemma lipschitzWith_one_equiv_pi_aux
  statement: LipschitzWith 1 (equiv A (Π i, E i))
  proof: AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv Complex A (Π i, E i)) 1 by
    simpa using! norm_equiv_le_norm_pi

中文:
引理 lipschitzWith_one_equiv_pi_aux
  结论: LipschitzWith 1 (equiv A (Π i, E i))
  证明: AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv Complex A (Π i, E i)) 1 by
    simpa using! norm_equiv_le_norm_pi
-/
private lemma lipschitzWith_one_equiv_pi_aux : LipschitzWith 1 (equiv A (Π i, E i)) :=
AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv Complex A (Π i, E i)) 1 by
    simpa using! norm_equiv_le_norm_pi

/--
lemma `uniformity_pi_eq_aux` / 引理 `uniformity_pi_eq_aux`

English:
lemma uniformity_pi_eq_aux
  proof: uniformity_eq_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux

中文:
引理 uniformity_pi_eq_aux
  证明: uniformity_eq_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux
-/
private lemma uniformity_pi_eq_aux :
    𝓤[(inferInstance : UniformSpace (Π i, E i)).comap <| equiv A _] = 𝓤 C⋆ᵐᵒᵈ(A, Π i, E i) :=
  uniformity_eq_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux

/--
lemma `isBounded_pi_iff_aux` / 引理 `isBounded_pi_iff_aux`

English:
lemma isBounded_pi_iff_aux
  given: (s : Set C⋆ᵐᵒᵈ(A, Π i, E i))
  proof: isBounded_iff_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux s

中文:
引理 isBounded_pi_iff_aux
  条件: (s : 集合 C⋆ᵐᵒᵈ(A, Π i, E i))
  证明: isBounded_iff_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux s
-/
private lemma isBounded_pi_iff_aux (s : Set C⋆ᵐᵒᵈ(A, Π i, E i)) :
    @IsBounded _ (induced <| equiv A (Π i, E i)) s ↔ IsBounded s :=
  isBounded_iff_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux s

end Aux

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i)
  body: fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_

中文:
实例 :
  签名: 赋范交换加群 C⋆ᵐᵒᵈ(A, Π i, E i)
  定义体: fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_

Depends on / 依赖: fast_instance, normedSpaceCore, ofCoreReplaceAll
-/
noncomputable instance : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) :=
  fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_
where finally
  exacts [uniformity_pi_eq_aux, isBounded_pi_iff_aux]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedSpace Complex C⋆ᵐᵒᵈ(A, Π i, E i)
  body: .ofCore (normedSpaceCore A)

中文:
实例 :
  签名: 赋范空间 复形 C⋆ᵐᵒᵈ(A, Π i, E i)
  定义体: .ofCore (normedSpaceCore A)

Depends on / 依赖: normedSpaceCore, ofCore
-/
noncomputable instance : NormedSpace Complex C⋆ᵐᵒᵈ(A, Π i, E i) := .ofCore (normedSpaceCore A)

end Pi

/-! ## Inner product spaces as C⋆-modules -/

section InnerProductSpace

open ComplexOrder

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]

open scoped InnerProductSpace in
/--
Instance `instCStarModuleComplex` / 实例 `instCStarModuleComplex`

English:
instance instCStarModuleComplex
  signature: : CStarModule Complex E where
  body: ⟪x, y⟫_Complex
  inner_add_right := by simp [_root_.inner_add_right]
  inner_self_nonneg {x} := by
    rw [← inner_self_ofReal_re]; rw [RCLike.ofReal_nonneg]
    exact inner_self_nonneg
  inner_self := by simp
  inner_op_smul_right := by simp [inner_smul_right]
  inner_smul_right_complex := by simp [inner_smul_right, smul_eq_mul]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_re_inner x

中文:
实例 instCStarModuleComplex
  签名: : CStar模 复形 E where
  定义体: ⟪x, y⟫_Complex
  inner_add_right := by simp [_root_.inner_add_right]
  inner_self_nonneg {x} := by
    rw [← inner_self_ofReal_re]; rw [RCLike.ofReal_nonneg]
    exact inner_self_nonneg
  inner_self := by simp
  inner_op_smul_right := by simp [inner_smul_right]
  inner_smul_right_complex := by simp [inner_smul_right, smul_eq_mul]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_re_inner x

Depends on / 依赖: _Complex
-/
noncomputable instance instCStarModuleComplex : CStarModule Complex E where
  inner x y := ⟪x, y⟫_Complex
  inner_add_right := by simp [_root_.inner_add_right]
  inner_self_nonneg {x} := by
    rw [← inner_self_ofReal_re]; rw [RCLike.ofReal_nonneg]
    exact inner_self_nonneg
  inner_self := by simp
  inner_op_smul_right := by simp [inner_smul_right]
  inner_smul_right_complex := by simp [inner_smul_right, smul_eq_mul]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_re_inner x

-- Ensures that the two ways to obtain `CStarModule ℂᵐᵒᵖ ℂ` are definitionally equal.
example : instCStarModule (A := Complex) = instCStarModuleComplex := by with_reducible_and_instances rfl

/-- Ensures that the two `Inner ℂ ℂ` instances are definitionally equal. Note that this cannot be at
reducible and instances transparency because the one from `InnerProductSpace` uses `StarRingEnd`
whereas `WithCStarModule.instCStarModule.toInner` uses `star` since `A` may not be commutative. -/
example : (toInner : Inner Complex Complex) = WithCStarModule.instCStarModule.toInner := rfl

end InnerProductSpace

end WithCStarModule
