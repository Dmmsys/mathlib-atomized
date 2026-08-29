/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

In this fact we use the fact that `ℂ` is naturally homeomorphic to `ℝ × ℝ` to deduce some
topological properties of `Complex.re` and `Complex.im`.

## Main statements

Each statement about `Complex.re` listed below has a counterpart about `Complex.im`.

* `Complex.isHomeomorphicTrivialFiberBundle_re`: `Complex.re` turns `ℂ` into a trivial
  topological fiber bundle over `ℝ`;
* `Complex.isOpenMap_re`, `Complex.isQuotientMap_re`: in particular, `Complex.re` is an open map
  and is a quotient map;
* `Complex.interior_preimage_re`, `Complex.closure_preimage_re`, `Complex.frontier_preimage_re`:
  formulas for `interior (Complex.re ⁻¹' s)` etc;
* `Complex.interior_setOfPred_re_le` etc: particular cases of the above formulas in the cases
  when `s` is one of the infinite intervals `Set.Ioi a`, `Set.Ici a`, `Set.Iio a`, and `Set.Iic a`,
  formulated as `interior {z : ℂ | z.re ≤ a} = {z | z.re < a}` etc.

## Tags

complex, real part, imaginary part, closure, interior, frontier
-/

public section

open Set Topology

noncomputable section

namespace Complex

/--
theorem `isHomeomorphicTrivialFiberBundle_re` / 定理 `isHomeomorphicTrivialFiberBundle_re`

English:
theorem isHomeomorphicTrivialFiberBundle_re
  statement: IsHomeomorphicTrivialFiberBundle Real re
  proof: ⟨equivRealProdCLM.toHomeomorph, fun _ => rfl⟩

中文:
定理 isHomeomorphicTrivialFiberBundle_re
  结论: IsHomeomorphicTrivialFiberBundle 实数 re
  证明: ⟨equivRealProdCLM.toHomeomorph, fun _ => rfl⟩

Depends on / 依赖: equivRealProdCLM, equivRealProdCLM.toHomeomorph, toHomeomorph
-/
theorem isHomeomorphicTrivialFiberBundle_re : IsHomeomorphicTrivialFiberBundle Real re :=
  ⟨equivRealProdCLM.toHomeomorph, fun _ => rfl⟩

/--
theorem `isHomeomorphicTrivialFiberBundle_im` / 定理 `isHomeomorphicTrivialFiberBundle_im`

English:
theorem isHomeomorphicTrivialFiberBundle_im
  statement: IsHomeomorphicTrivialFiberBundle Real im
  proof: ⟨equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm Real Real), fun _ => rfl⟩

中文:
定理 isHomeomorphicTrivialFiberBundle_im
  结论: IsHomeomorphicTrivialFiberBundle 实数 im
  证明: ⟨equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm Real Real), fun _ => rfl⟩

Depends on / 依赖: Homeomorph, Homeomorph.prodComm, equivRealProdCLM, equivRealProdCLM.toHomeomorph.trans, prodComm, toHomeomorph
-/
theorem isHomeomorphicTrivialFiberBundle_im : IsHomeomorphicTrivialFiberBundle Real im :=
  ⟨equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm Real Real), fun _ => rfl⟩

/--
theorem `isOpenMap_re` / 定理 `isOpenMap_re`

English:
theorem isOpenMap_re
  statement: IsOpenMap re
  proof: isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj

中文:
定理 isOpenMap_re
  结论: IsOpenMap re
  证明: isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj

Depends on / 依赖: isHomeomorphicTrivialFiberBundle_re, isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj, isOpenMap_proj
-/
theorem isOpenMap_re : IsOpenMap re :=
  isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj

/--
theorem `isOpenMap_im` / 定理 `isOpenMap_im`

English:
theorem isOpenMap_im
  statement: IsOpenMap im
  proof: isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj

中文:
定理 isOpenMap_im
  结论: IsOpenMap im
  证明: isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj

Depends on / 依赖: isHomeomorphicTrivialFiberBundle_im, isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj, isOpenMap_proj
-/
theorem isOpenMap_im : IsOpenMap im :=
  isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj

/--
theorem `isQuotientMap_re` / 定理 `isQuotientMap_re`

English:
theorem isQuotientMap_re
  statement: IsQuotientMap re
  proof: isHomeomorphicTrivialFiberBundle_re.isQuotientMap_proj

中文:
定理 isQuotientMap_re
  结论: IsQuotientMap re
  证明: isHomeomorphicTrivialFiberBundle_re.isQuotientMap_proj

Depends on / 依赖: isHomeomorphicTrivialFiberBundle_re, isHomeomorphicTrivialFiberBundle_re.isQuotientMap_proj, isQuotientMap_proj
-/
theorem isQuotientMap_re : IsQuotientMap re :=
  isHomeomorphicTrivialFiberBundle_re.isQuotientMap_proj

/--
theorem `isQuotientMap_im` / 定理 `isQuotientMap_im`

English:
theorem isQuotientMap_im
  statement: IsQuotientMap im
  proof: isHomeomorphicTrivialFiberBundle_im.isQuotientMap_proj

中文:
定理 isQuotientMap_im
  结论: IsQuotientMap im
  证明: isHomeomorphicTrivialFiberBundle_im.isQuotientMap_proj

Depends on / 依赖: isHomeomorphicTrivialFiberBundle_im, isHomeomorphicTrivialFiberBundle_im.isQuotientMap_proj, isQuotientMap_proj
-/
theorem isQuotientMap_im : IsQuotientMap im :=
  isHomeomorphicTrivialFiberBundle_im.isQuotientMap_proj

/--
theorem `interior_preimage_re` / 定理 `interior_preimage_re`

English:
theorem interior_preimage_re
  given: (s : Set Real)
  statement: interior (re ⁻¹' s) = re ⁻¹' interior s
  proof: (isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re _).symm

中文:
定理 interior_preimage_re
  条件: (s : Set 实数)
  结论: interior (re ⁻¹' s) = re ⁻¹' interior s
  证明: (isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re _).symm

Depends on / 依赖: continuous_re, isOpenMap_re, isOpenMap_re.preimage_interior_eq_interior_preimage, preimage_interior_eq_interior_preimage
-/
theorem interior_preimage_re (s : Set Real) : interior (re ⁻¹' s) = re ⁻¹' interior s :=
  (isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re _).symm

/--
theorem `interior_preimage_im` / 定理 `interior_preimage_im`

English:
theorem interior_preimage_im
  given: (s : Set Real)
  statement: interior (im ⁻¹' s) = im ⁻¹' interior s
  proof: (isOpenMap_im.preimage_interior_eq_interior_preimage continuous_im _).symm

中文:
定理 interior_preimage_im
  条件: (s : Set 实数)
  结论: interior (im ⁻¹' s) = im ⁻¹' interior s
  证明: (isOpenMap_im.preimage_interior_eq_interior_preimage continuous_im _).symm

Depends on / 依赖: continuous_im, isOpenMap_im, isOpenMap_im.preimage_interior_eq_interior_preimage, preimage_interior_eq_interior_preimage
-/
theorem interior_preimage_im (s : Set Real) : interior (im ⁻¹' s) = im ⁻¹' interior s :=
  (isOpenMap_im.preimage_interior_eq_interior_preimage continuous_im _).symm

/--
theorem `closure_preimage_re` / 定理 `closure_preimage_re`

English:
theorem closure_preimage_re
  given: (s : Set Real)
  statement: closure (re ⁻¹' s) = re ⁻¹' closure s
  proof: (isOpenMap_re.preimage_closure_eq_closure_preimage continuous_re _).symm

中文:
定理 closure_preimage_re
  条件: (s : Set 实数)
  结论: closure (re ⁻¹' s) = re ⁻¹' closure s
  证明: (isOpenMap_re.preimage_closure_eq_closure_preimage continuous_re _).symm

Depends on / 依赖: continuous_re, isOpenMap_re, isOpenMap_re.preimage_closure_eq_closure_preimage, preimage_closure_eq_closure_preimage
-/
theorem closure_preimage_re (s : Set Real) : closure (re ⁻¹' s) = re ⁻¹' closure s :=
  (isOpenMap_re.preimage_closure_eq_closure_preimage continuous_re _).symm

/--
theorem `closure_preimage_im` / 定理 `closure_preimage_im`

English:
theorem closure_preimage_im
  given: (s : Set Real)
  statement: closure (im ⁻¹' s) = im ⁻¹' closure s
  proof: (isOpenMap_im.preimage_closure_eq_closure_preimage continuous_im _).symm

中文:
定理 closure_preimage_im
  条件: (s : Set 实数)
  结论: closure (im ⁻¹' s) = im ⁻¹' closure s
  证明: (isOpenMap_im.preimage_closure_eq_closure_preimage continuous_im _).symm

Depends on / 依赖: continuous_im, isOpenMap_im, isOpenMap_im.preimage_closure_eq_closure_preimage, preimage_closure_eq_closure_preimage
-/
theorem closure_preimage_im (s : Set Real) : closure (im ⁻¹' s) = im ⁻¹' closure s :=
  (isOpenMap_im.preimage_closure_eq_closure_preimage continuous_im _).symm

/--
theorem `frontier_preimage_re` / 定理 `frontier_preimage_re`

English:
theorem frontier_preimage_re
  given: (s : Set Real)
  statement: frontier (re ⁻¹' s) = re ⁻¹' frontier s
  proof: (isOpenMap_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm

中文:
定理 frontier_preimage_re
  条件: (s : Set 实数)
  结论: frontier (re ⁻¹' s) = re ⁻¹' frontier s
  证明: (isOpenMap_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm

Depends on / 依赖: continuous_re, isOpenMap_re, isOpenMap_re.preimage_frontier_eq_frontier_preimage, preimage_frontier_eq_frontier_preimage
-/
theorem frontier_preimage_re (s : Set Real) : frontier (re ⁻¹' s) = re ⁻¹' frontier s :=
  (isOpenMap_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm

/--
theorem `frontier_preimage_im` / 定理 `frontier_preimage_im`

English:
theorem frontier_preimage_im
  given: (s : Set Real)
  statement: frontier (im ⁻¹' s) = im ⁻¹' frontier s
  proof: (isOpenMap_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm

@[simp]

中文:
定理 frontier_preimage_im
  条件: (s : Set 实数)
  结论: frontier (im ⁻¹' s) = im ⁻¹' frontier s
  证明: (isOpenMap_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm

@[simp]

Depends on / 依赖: continuous_im, isOpenMap_im, isOpenMap_im.preimage_frontier_eq_frontier_preimage, preimage_frontier_eq_frontier_preimage
-/
theorem frontier_preimage_im (s : Set Real) : frontier (im ⁻¹' s) = im ⁻¹' frontier s :=
  (isOpenMap_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm

@[simp]
/--
theorem `interior_setOfPred_re_le` / 定理 `interior_setOfPred_re_le`

English:
theorem interior_setOfPred_re_le
  given: (a : Real)
  statement: interior { z : Complex | z.re <= a } = { z | z.re < a }
  proof: by
  simpa only [interior_Iic] using! interior_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_re_le := interior_setOfPred_re_le

@[simp]

中文:
定理 interior_setOfPred_re_le
  条件: (a : 实数)
  结论: interior { z : Complex | z.re <= a } = { z | z.re < a }
  证明: by
  simpa only [interior_Iic] using! interior_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_re_le := interior_setOfPred_re_le

@[simp]

Depends on / 依赖: interior_Iic, interior_preimage_re
-/
theorem interior_setOfPred_re_le (a : Real) : interior { z : Complex | z.re <= a } = { z | z.re < a } := by
  simpa only [interior_Iic] using! interior_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_re_le := interior_setOfPred_re_le

@[simp]
/--
theorem `interior_setOfPred_im_le` / 定理 `interior_setOfPred_im_le`

English:
theorem interior_setOfPred_im_le
  given: (a : Real)
  statement: interior { z : Complex | z.im <= a } = { z | z.im < a }
  proof: by
  simpa only [interior_Iic] using! interior_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_im_le := interior_setOfPred_im_le

@[simp]

中文:
定理 interior_setOfPred_im_le
  条件: (a : 实数)
  结论: interior { z : Complex | z.im <= a } = { z | z.im < a }
  证明: by
  simpa only [interior_Iic] using! interior_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_im_le := interior_setOfPred_im_le

@[simp]

Depends on / 依赖: interior_Iic, interior_preimage_im
-/
theorem interior_setOfPred_im_le (a : Real) : interior { z : Complex | z.im <= a } = { z | z.im < a } := by
  simpa only [interior_Iic] using! interior_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_im_le := interior_setOfPred_im_le

@[simp]
/--
theorem `interior_setOfPred_le_re` / 定理 `interior_setOfPred_le_re`

English:
theorem interior_setOfPred_le_re
  given: (a : Real)
  statement: interior { z : Complex | a <= z.re } = { z | a < z.re }
  proof: by
  simpa only [interior_Ici] using! interior_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_re := interior_setOfPred_le_re

@[simp]

中文:
定理 interior_setOfPred_le_re
  条件: (a : 实数)
  结论: interior { z : Complex | a <= z.re } = { z | a < z.re }
  证明: by
  simpa only [interior_Ici] using! interior_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_re := interior_setOfPred_le_re

@[simp]

Depends on / 依赖: interior_Ici, interior_preimage_re
-/
theorem interior_setOfPred_le_re (a : Real) : interior { z : Complex | a <= z.re } = { z | a < z.re } := by
  simpa only [interior_Ici] using! interior_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_re := interior_setOfPred_le_re

@[simp]
/--
theorem `interior_setOfPred_le_im` / 定理 `interior_setOfPred_le_im`

English:
theorem interior_setOfPred_le_im
  given: (a : Real)
  statement: interior { z : Complex | a <= z.im } = { z | a < z.im }
  proof: by
  simpa only [interior_Ici] using! interior_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_im := interior_setOfPred_le_im

@[simp]

中文:
定理 interior_setOfPred_le_im
  条件: (a : 实数)
  结论: interior { z : Complex | a <= z.im } = { z | a < z.im }
  证明: by
  simpa only [interior_Ici] using! interior_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_im := interior_setOfPred_le_im

@[simp]

Depends on / 依赖: interior_Ici, interior_preimage_im
-/
theorem interior_setOfPred_le_im (a : Real) : interior { z : Complex | a <= z.im } = { z | a < z.im } := by
  simpa only [interior_Ici] using! interior_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias interior_setOf_le_im := interior_setOfPred_le_im

@[simp]
/--
theorem `closure_setOfPred_re_lt` / 定理 `closure_setOfPred_re_lt`

English:
theorem closure_setOfPred_re_lt
  given: (a : Real)
  statement: closure { z : Complex | z.re < a } = { z | z.re <= a }
  proof: by
  simpa only [closure_Iio] using! closure_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_re_lt := closure_setOfPred_re_lt

@[simp]

中文:
定理 closure_setOfPred_re_lt
  条件: (a : 实数)
  结论: closure { z : Complex | z.re < a } = { z | z.re <= a }
  证明: by
  simpa only [closure_Iio] using! closure_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_re_lt := closure_setOfPred_re_lt

@[simp]

Depends on / 依赖: closure_Iio, closure_preimage_re
-/
theorem closure_setOfPred_re_lt (a : Real) : closure { z : Complex | z.re < a } = { z | z.re <= a } := by
  simpa only [closure_Iio] using! closure_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_re_lt := closure_setOfPred_re_lt

@[simp]
/--
theorem `closure_setOfPred_im_lt` / 定理 `closure_setOfPred_im_lt`

English:
theorem closure_setOfPred_im_lt
  given: (a : Real)
  statement: closure { z : Complex | z.im < a } = { z | z.im <= a }
  proof: by
  simpa only [closure_Iio] using! closure_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_im_lt := closure_setOfPred_im_lt

@[simp]

中文:
定理 closure_setOfPred_im_lt
  条件: (a : 实数)
  结论: closure { z : Complex | z.im < a } = { z | z.im <= a }
  证明: by
  simpa only [closure_Iio] using! closure_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_im_lt := closure_setOfPred_im_lt

@[simp]

Depends on / 依赖: closure_Iio, closure_preimage_im
-/
theorem closure_setOfPred_im_lt (a : Real) : closure { z : Complex | z.im < a } = { z | z.im <= a } := by
  simpa only [closure_Iio] using! closure_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_im_lt := closure_setOfPred_im_lt

@[simp]
/--
theorem `closure_setOfPred_lt_re` / 定理 `closure_setOfPred_lt_re`

English:
theorem closure_setOfPred_lt_re
  given: (a : Real)
  statement: closure { z : Complex | a < z.re } = { z | a <= z.re }
  proof: by
  simpa only [closure_Ioi] using! closure_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_lt_re := closure_setOfPred_lt_re

@[simp]

中文:
定理 closure_setOfPred_lt_re
  条件: (a : 实数)
  结论: closure { z : Complex | a < z.re } = { z | a <= z.re }
  证明: by
  simpa only [closure_Ioi] using! closure_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_lt_re := closure_setOfPred_lt_re

@[simp]

Depends on / 依赖: closure_Ioi, closure_preimage_re
-/
theorem closure_setOfPred_lt_re (a : Real) : closure { z : Complex | a < z.re } = { z | a <= z.re } := by
  simpa only [closure_Ioi] using! closure_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias closure_setOf_lt_re := closure_setOfPred_lt_re

@[simp]
/--
theorem `closure_setOfPred_lt_im` / 定理 `closure_setOfPred_lt_im`

English:
theorem closure_setOfPred_lt_im
  given: (a : Real)
  statement: closure { z : Complex | a < z.im } = { z | a <= z.im }
  proof: by
  simpa only [closure_Ioi] using! closure_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_lt_im := closure_setOfPred_lt_im

@[simp]

中文:
定理 closure_setOfPred_lt_im
  条件: (a : 实数)
  结论: closure { z : Complex | a < z.im } = { z | a <= z.im }
  证明: by
  simpa only [closure_Ioi] using! closure_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_lt_im := closure_setOfPred_lt_im

@[simp]

Depends on / 依赖: closure_Ioi, closure_preimage_im
-/
theorem closure_setOfPred_lt_im (a : Real) : closure { z : Complex | a < z.im } = { z | a <= z.im } := by
  simpa only [closure_Ioi] using! closure_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")] alias closure_setOf_lt_im := closure_setOfPred_lt_im

@[simp]
/--
theorem `frontier_setOfPred_re_le` / 定理 `frontier_setOfPred_re_le`

English:
theorem frontier_setOfPred_re_le
  given: (a : Real)
  statement: frontier { z : Complex | z.re <= a } = { z | z.re = a }
  proof: by
  simpa only [frontier_Iic] using! frontier_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_le := frontier_setOfPred_re_le

@[simp]

中文:
定理 frontier_setOfPred_re_le
  条件: (a : 实数)
  结论: frontier { z : Complex | z.re <= a } = { z | z.re = a }
  证明: by
  simpa only [frontier_Iic] using! frontier_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_le := frontier_setOfPred_re_le

@[simp]

Depends on / 依赖: continuous, frontier_Iic, frontier_preimage_re, map_contDiff
-/
theorem frontier_setOfPred_re_le (a : Real) : frontier { z : Complex | z.re <= a } = { z | z.re = a } := by
  simpa only [frontier_Iic] using! frontier_preimage_re (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_le := frontier_setOfPred_re_le

@[simp]
/--
theorem `frontier_setOfPred_im_le` / 定理 `frontier_setOfPred_im_le`

English:
theorem frontier_setOfPred_im_le
  given: (a : Real)
  statement: frontier { z : Complex | z.im <= a } = { z | z.im = a }
  proof: by
  simpa only [frontier_Iic] using! frontier_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_le := frontier_setOfPred_im_le

@[simp]

中文:
定理 frontier_setOfPred_im_le
  条件: (a : 实数)
  结论: frontier { z : Complex | z.im <= a } = { z | z.im = a }
  证明: by
  simpa only [frontier_Iic] using! frontier_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_le := frontier_setOfPred_im_le

@[simp]

Depends on / 依赖: BoundedContinuousFunction, BoundedContinuousFunction.ofNormedAddCommGroup, bounded_above_of_compact_support, frontier_Iic, frontier_preimage_im, map_bounded, map_continuous, map_hasCompactSupport, ofNormedAddCommGroup
-/
theorem frontier_setOfPred_im_le (a : Real) : frontier { z : Complex | z.im <= a } = { z | z.im = a } := by
  simpa only [frontier_Iic] using! frontier_preimage_im (Iic a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_le := frontier_setOfPred_im_le

@[simp]
/--
theorem `frontier_setOfPred_le_re` / 定理 `frontier_setOfPred_le_re`

English:
theorem frontier_setOfPred_le_re
  given: (a : Real)
  statement: frontier { z : Complex | a <= z.re } = { z | z.re = a }
  proof: by
  simpa only [frontier_Ici] using! frontier_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re := frontier_setOfPred_le_re

@[simp]

中文:
定理 frontier_setOfPred_le_re
  条件: (a : 实数)
  结论: frontier { z : Complex | a <= z.re } = { z | z.re = a }
  证明: by
  simpa only [frontier_Ici] using! frontier_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re := frontier_setOfPred_le_re

@[simp]

Depends on / 依赖: frontier_Ici, frontier_preimage_re
-/
theorem frontier_setOfPred_le_re (a : Real) : frontier { z : Complex | a <= z.re } = { z | z.re = a } := by
  simpa only [frontier_Ici] using! frontier_preimage_re (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re := frontier_setOfPred_le_re

@[simp]
/--
theorem `frontier_setOfPred_le_im` / 定理 `frontier_setOfPred_le_im`

English:
theorem frontier_setOfPred_le_im
  given: (a : Real)
  statement: frontier { z : Complex | a <= z.im } = { z | z.im = a }
  proof: by
  simpa only [frontier_Ici] using! frontier_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_im := frontier_setOfPred_le_im

@[simp]

中文:
定理 frontier_setOfPred_le_im
  条件: (a : 实数)
  结论: frontier { z : Complex | a <= z.im } = { z | z.im = a }
  证明: by
  simpa only [frontier_Ici] using! frontier_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_im := frontier_setOfPred_le_im

@[simp]

Depends on / 依赖: frontier_Ici, frontier_preimage_im
-/
theorem frontier_setOfPred_le_im (a : Real) : frontier { z : Complex | a <= z.im } = { z | z.im = a } := by
  simpa only [frontier_Ici] using! frontier_preimage_im (Ici a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_im := frontier_setOfPred_le_im

@[simp]
/--
theorem `frontier_setOfPred_re_lt` / 定理 `frontier_setOfPred_re_lt`

English:
theorem frontier_setOfPred_re_lt
  given: (a : Real)
  statement: frontier { z : Complex | z.re < a } = { z | z.re = a }
  proof: by
  simpa only [frontier_Iio] using! frontier_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_lt := frontier_setOfPred_re_lt

@[simp]

中文:
定理 frontier_setOfPred_re_lt
  条件: (a : 实数)
  结论: frontier { z : Complex | z.re < a } = { z | z.re = a }
  证明: by
  simpa only [frontier_Iio] using! frontier_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_lt := frontier_setOfPred_re_lt

@[simp]

Depends on / 依赖: frontier_Iio, frontier_preimage_re
-/
theorem frontier_setOfPred_re_lt (a : Real) : frontier { z : Complex | z.re < a } = { z | z.re = a } := by
  simpa only [frontier_Iio] using! frontier_preimage_re (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_re_lt := frontier_setOfPred_re_lt

@[simp]
/--
theorem `frontier_setOfPred_im_lt` / 定理 `frontier_setOfPred_im_lt`

English:
theorem frontier_setOfPred_im_lt
  given: (a : Real)
  statement: frontier { z : Complex | z.im < a } = { z | z.im = a }
  proof: by
  simpa only [frontier_Iio] using! frontier_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_lt := frontier_setOfPred_im_lt

@[simp]

中文:
定理 frontier_setOfPred_im_lt
  条件: (a : 实数)
  结论: frontier { z : Complex | z.im < a } = { z | z.im = a }
  证明: by
  simpa only [frontier_Iio] using! frontier_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_lt := frontier_setOfPred_im_lt

@[simp]

Depends on / 依赖: frontier_Iio, frontier_preimage_im
-/
theorem frontier_setOfPred_im_lt (a : Real) : frontier { z : Complex | z.im < a } = { z | z.im = a } := by
  simpa only [frontier_Iio] using! frontier_preimage_im (Iio a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_im_lt := frontier_setOfPred_im_lt

@[simp]
/--
theorem `frontier_setOfPred_lt_re` / 定理 `frontier_setOfPred_lt_re`

English:
theorem frontier_setOfPred_lt_re
  given: (a : Real)
  statement: frontier { z : Complex | a < z.re } = { z | z.re = a }
  proof: by
  simpa only [frontier_Ioi] using! frontier_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_re := frontier_setOfPred_lt_re

@[simp]

中文:
定理 frontier_setOfPred_lt_re
  条件: (a : 实数)
  结论: frontier { z : Complex | a < z.re } = { z | z.re = a }
  证明: by
  simpa only [frontier_Ioi] using! frontier_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_re := frontier_setOfPred_lt_re

@[simp]

Depends on / 依赖: frontier_Ioi, frontier_preimage_re
-/
theorem frontier_setOfPred_lt_re (a : Real) : frontier { z : Complex | a < z.re } = { z | z.re = a } := by
  simpa only [frontier_Ioi] using! frontier_preimage_re (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_re := frontier_setOfPred_lt_re

@[simp]
/--
theorem `frontier_setOfPred_lt_im` / 定理 `frontier_setOfPred_lt_im`

English:
theorem frontier_setOfPred_lt_im
  given: (a : Real)
  statement: frontier { z : Complex | a < z.im } = { z | z.im = a }
  proof: by
  simpa only [frontier_Ioi] using! frontier_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_im := frontier_setOfPred_lt_im

中文:
定理 frontier_setOfPred_lt_im
  条件: (a : 实数)
  结论: frontier { z : Complex | a < z.im } = { z | z.im = a }
  证明: by
  simpa only [frontier_Ioi] using! frontier_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_im := frontier_setOfPred_lt_im

Depends on / 依赖: frontier_Ioi, frontier_preimage_im
-/
theorem frontier_setOfPred_lt_im (a : Real) : frontier { z : Complex | a < z.im } = { z | z.im = a } := by
  simpa only [frontier_Ioi] using! frontier_preimage_im (Ioi a)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_lt_im := frontier_setOfPred_lt_im

/--
theorem `closure_reProdIm` / 定理 `closure_reProdIm`

English:
theorem closure_reProdIm
  given: (s t : Set Real)
  statement: closure (s ×Complex t) = closure s ×Complex closure t
  proof: by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_closure] using! @closure_prod_eq _ _ _ _ s t

中文:
定理 closure_reProdIm
  条件: (s t : Set 实数)
  结论: closure (s ×Complex t) = closure s ×Complex closure t
  证明: by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_closure] using! @closure_prod_eq _ _ _ _ s t

Depends on / 依赖: closure_prod_eq, equivRealProdCLM, equivRealProdCLM.symm.toHomeomorph.preimage_closure, equivRealProdCLM.symm.toHomeomorph.surjective, preimage_closure, preimage_eq_preimage, surjective, toHomeomorph
-/
theorem closure_reProdIm (s t : Set Real) : closure (s ×Complex t) = closure s ×Complex closure t := by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_closure] using! @closure_prod_eq _ _ _ _ s t

/--
theorem `interior_reProdIm` / 定理 `interior_reProdIm`

English:
theorem interior_reProdIm
  given: (s t : Set Real)
  statement: interior (s ×Complex t) = interior s ×Complex interior t
  proof: by
  rw [reProdIm]; rw [reProdIm]; rw [interior_inter]; rw [interior_preimage_re]; rw [interior_preimage_im]

中文:
定理 interior_reProdIm
  条件: (s t : Set 实数)
  结论: interior (s ×Complex t) = interior s ×Complex interior t
  证明: by
  rw [reProdIm]; rw [reProdIm]; rw [interior_inter]; rw [interior_preimage_re]; rw [interior_preimage_im]

Depends on / 依赖: interior_inter, interior_preimage_im, interior_preimage_re, reProdIm
-/
theorem interior_reProdIm (s t : Set Real) : interior (s ×Complex t) = interior s ×Complex interior t := by
  rw [reProdIm]; rw [reProdIm]; rw [interior_inter]; rw [interior_preimage_re]; rw [interior_preimage_im]

/--
theorem `frontier_reProdIm` / 定理 `frontier_reProdIm`

English:
theorem frontier_reProdIm
  given: (s t : Set Real)
  proof: by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_frontier] using! frontier_prod_eq s t

中文:
定理 frontier_reProdIm
  条件: (s t : Set 实数)
  证明: by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_frontier] using! frontier_prod_eq s t

Depends on / 依赖: equivRealProdCLM, equivRealProdCLM.symm.toHomeomorph.preimage_frontier, equivRealProdCLM.symm.toHomeomorph.surjective, frontier_prod_eq, preimage_eq_preimage, preimage_frontier, surjective, toHomeomorph
-/
theorem frontier_reProdIm (s t : Set Real) :
    frontier (s ×Complex t) = closure s ×Complex frontier t union frontier s ×Complex closure t := by
  simpa only [← preimage_eq_preimage equivRealProdCLM.symm.toHomeomorph.surjective,
    equivRealProdCLM.symm.toHomeomorph.preimage_frontier] using! frontier_prod_eq s t

/--
theorem `frontier_setOfPred_le_re_and_le_im` / 定理 `frontier_setOfPred_le_re_and_le_im`

English:
theorem frontier_setOfPred_le_re_and_le_im
  given: (a b : Real)
  proof: by
  simpa only [closure_Ici, frontier_Ici] using! frontier_reProdIm (Ici a) (Ici b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_le_im := frontier_setOfPred_le_re_and_le_im

中文:
定理 frontier_setOfPred_le_re_and_le_im
  条件: (a b : 实数)
  证明: by
  simpa only [closure_Ici, frontier_Ici] using! frontier_reProdIm (Ici a) (Ici b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_le_im := frontier_setOfPred_le_re_and_le_im

Depends on / 依赖: closure_Ici, frontier_Ici, frontier_reProdIm
-/
theorem frontier_setOfPred_le_re_and_le_im (a b : Real) :
    frontier { z | a <= re z ∧ b <= im z } = { z | a <= re z ∧ im z = b ∨ re z = a ∧ b <= im z } := by
  simpa only [closure_Ici, frontier_Ici] using! frontier_reProdIm (Ici a) (Ici b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_le_im := frontier_setOfPred_le_re_and_le_im

/--
theorem `frontier_setOfPred_le_re_and_im_le` / 定理 `frontier_setOfPred_le_re_and_im_le`

English:
theorem frontier_setOfPred_le_re_and_im_le
  given: (a b : Real)
  proof: by
  simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic] using!
    frontier_reProdIm (Ici a) (Iic b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_im_le := frontier_setOfPred_le_re_and_im_le

中文:
定理 frontier_setOfPred_le_re_and_im_le
  条件: (a b : 实数)
  证明: by
  simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic] using!
    frontier_reProdIm (Ici a) (Iic b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_im_le := frontier_setOfPred_le_re_and_im_le

Depends on / 依赖: closure_Ici, closure_Iic, frontier_Ici, frontier_Iic, frontier_reProdIm
-/
theorem frontier_setOfPred_le_re_and_im_le (a b : Real) :
    frontier { z | a <= re z ∧ im z <= b } = { z | a <= re z ∧ im z = b ∨ re z = a ∧ im z <= b } := by
  simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic] using!
    frontier_reProdIm (Ici a) (Iic b)

@[deprecated (since := "2026-07-09")]
alias frontier_setOf_le_re_and_im_le := frontier_setOfPred_le_re_and_im_le

end Complex

open Complex Metric

variable {s t : Set Real}

/--
theorem `IsOpen.reProdIm` / 定理 `IsOpen.reProdIm`

English:
theorem IsOpen.reProdIm
  given: (hs : IsOpen s) (ht : IsOpen t)
  statement: IsOpen (s ×Complex t)
  proof: (hs.preimage continuous_re).inter (ht.preimage continuous_im)

中文:
定理 IsOpen.reProdIm
  条件: (hs : IsOpen s) (ht : IsOpen t)
  结论: IsOpen (s ×Complex t)
  证明: (hs.preimage continuous_re).inter (ht.preimage continuous_im)

Depends on / 依赖: continuous_im, continuous_re, hs.preimage, ht.preimage, preimage
-/
theorem IsOpen.reProdIm (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×Complex t) :=
  (hs.preimage continuous_re).inter (ht.preimage continuous_im)

/--
theorem `IsClosed.reProdIm` / 定理 `IsClosed.reProdIm`

English:
theorem IsClosed.reProdIm
  given: (hs : IsClosed s) (ht : IsClosed t)
  statement: IsClosed (s ×Complex t)
  proof: (hs.preimage continuous_re).inter (ht.preimage continuous_im)

中文:
定理 IsClosed.reProdIm
  条件: (hs : IsClosed s) (ht : IsClosed t)
  结论: IsClosed (s ×Complex t)
  证明: (hs.preimage continuous_re).inter (ht.preimage continuous_im)

Depends on / 依赖: continuous_im, continuous_re, hs.preimage, ht.preimage, preimage
-/
theorem IsClosed.reProdIm (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ×Complex t) :=
  (hs.preimage continuous_re).inter (ht.preimage continuous_im)

/--
theorem `Bornology.IsBounded.reProdIm` / 定理 `Bornology.IsBounded.reProdIm`

English:
theorem Bornology.IsBounded.reProdIm
  given: (hs : IsBounded s) (ht : IsBounded t)
  statement: IsBounded (s ×Complex t)
  proof: antilipschitz_equivRealProd.isBounded_preimage (hs.prod ht)

中文:
定理 Bornology.IsBounded.reProdIm
  条件: (hs : IsBounded s) (ht : IsBounded t)
  结论: IsBounded (s ×Complex t)
  证明: antilipschitz_equivRealProd.isBounded_preimage (hs.prod ht)

Depends on / 依赖: antilipschitz_equivRealProd, antilipschitz_equivRealProd.isBounded_preimage, hs.prod, isBounded_preimage
-/
theorem Bornology.IsBounded.reProdIm (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×Complex t) :=
  antilipschitz_equivRealProd.isBounded_preimage (hs.prod ht)

section continuity

variable {α ι : Type*}

/--
lemma `TendstoUniformlyOn.re` / 引理 `TendstoUniformlyOn.re`

English:
lemma TendstoUniformlyOn.re
  statement: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex} {K : Set α}
  proof: by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_re hf

中文:
引理 TendstoUniformlyOn.re
  结论: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex} {K : Set α}
  证明: by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_re hf
-/
protected lemma TendstoUniformlyOn.re {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex} {K : Set α}
    (hf : TendstoUniformlyOn f g p K) :
    TendstoUniformlyOn (fun n x => (f n x).re) (fun y => (g y).re) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_re hf

/--
lemma `TendstoUniformly.re` / 引理 `TendstoUniformly.re`

English:
lemma TendstoUniformly.re
  statement: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex}
  proof: by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_re hf

中文:
引理 TendstoUniformly.re
  结论: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex}
  证明: by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_re hf
-/
protected lemma TendstoUniformly.re {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex}
    (hf : TendstoUniformly f g p) :
    TendstoUniformly (fun n x => (f n x).re) (fun y => (g y).re) p := by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_re hf

/--
lemma `TendstoUniformlyOn.im` / 引理 `TendstoUniformlyOn.im`

English:
lemma TendstoUniformlyOn.im
  statement: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex} {K : Set α}
  proof: by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_im hf

中文:
引理 TendstoUniformlyOn.im
  结论: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex} {K : Set α}
  证明: by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_im hf

Depends on / 依赖: const_smul, contDiff, f.contDiff.const_smul, f.hasCompactSupport.smul_left, hasCompactSupport, smul_left
-/
protected lemma TendstoUniformlyOn.im {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex} {K : Set α}
    (hf : TendstoUniformlyOn f g p K) :
    TendstoUniformlyOn (fun n x => (f n x).im) (fun y => (g y).im) p K := by
  apply UniformContinuous.comp_tendstoUniformlyOn uniformContinuous_im hf

/--
lemma `TendstoUniformly.im` / 引理 `TendstoUniformly.im`

English:
lemma TendstoUniformly.im
  statement: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex}
  proof: by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_im hf

中文:
引理 TendstoUniformly.im
  结论: {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex}
  证明: by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_im hf
-/
protected lemma TendstoUniformly.im {f : ι -> α -> Complex} {p : Filter ι} {g : α -> Complex}
    (hf : TendstoUniformly f g p) :
    TendstoUniformly (fun n x => (f n x).im) (fun y => (g y).im) p := by
  apply UniformContinuous.comp_tendstoUniformly uniformContinuous_im hf

end continuity
