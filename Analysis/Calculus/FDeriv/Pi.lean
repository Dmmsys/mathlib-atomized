/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Derivatives on pi-types.
-/

public section

variable {𝕜 ι : Type*} [DecidableEq ι] [NontriviallyNormedField 𝕜]
variable {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]

@[fun_prop]
/--
theorem `hasFDerivAt_update` / 定理 `hasFDerivAt_update`

English:
theorem hasFDerivAt_update
  given: (x : forall i, E i) {i : ι} (y : E i)
  proof: by
  rw [hasFDerivAt_pi]
  intro j
  rcases eq_or_ne j i with rfl | hij
  · simpa using! hasFDerivAt_id _
  · simpa [hij] using! hasFDerivAt_const _ _

@[fun_prop]

中文:
定理 hasFDerivAt_update
  条件: (x : 对任意 i, E i) {i : ι} (y : E i)
  证明: by
  rw [hasFDerivAt_pi]
  intro j
  rcases eq_or_ne j i with rfl | hij
  · simpa using! hasFDerivAt_id _
  · simpa [hij] using! hasFDerivAt_const _ _

@[fun_prop]

Depends on / 依赖: eq_or_ne, hasFDerivAt_const, hasFDerivAt_id, hasFDerivAt_pi
-/
theorem hasFDerivAt_update (x : forall i, E i) {i : ι} (y : E i) :
    HasFDerivAt (Function.update x i) (.pi (Pi.single i (.id 𝕜 (E i)))) y := by
  rw [hasFDerivAt_pi]
  intro j
  rcases eq_or_ne j i with rfl | hij
  · simpa using! hasFDerivAt_id _
  · simpa [hij] using! hasFDerivAt_const _ _

@[fun_prop]
/--
theorem `hasFDerivAt_single` / 定理 `hasFDerivAt_single`

English:
theorem hasFDerivAt_single
  given: {i : ι} (y : E i)
  proof: hasFDerivAt_update 0 y

中文:
定理 hasFDerivAt_single
  条件: {i : ι} (y : E i)
  证明: hasFDerivAt_update 0 y

Depends on / 依赖: hasFDerivAt_update
-/
theorem hasFDerivAt_single {i : ι} (y : E i) :
    HasFDerivAt (Pi.single i) (.pi (Pi.single i (.id 𝕜 (E i)))) y :=
  hasFDerivAt_update 0 y

/--
theorem `fderiv_update` / 定理 `fderiv_update`

English:
theorem fderiv_update
  given: (x : forall i, E i) {i : ι} (y : E i)
  proof: (hasFDerivAt_update x y).fderiv

中文:
定理 fderiv_update
  条件: (x : 对任意 i, E i) {i : ι} (y : E i)
  证明: (hasFDerivAt_update x y).fderiv

Depends on / 依赖: fderiv, hasFDerivAt_update
-/
theorem fderiv_update (x : forall i, E i) {i : ι} (y : E i) :
    fderiv 𝕜 (Function.update x i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  (hasFDerivAt_update x y).fderiv

/--
theorem `fderiv_single` / 定理 `fderiv_single`

English:
theorem fderiv_single
  given: {i : ι} (y : E i)
  proof: fderiv_update 0 y

中文:
定理 fderiv_single
  条件: {i : ι} (y : E i)
  证明: fderiv_update 0 y

Depends on / 依赖: fderiv_update
-/
theorem fderiv_single {i : ι} (y : E i) :
    fderiv 𝕜 (Pi.single i) y = .pi (Pi.single i (.id 𝕜 (E i))) :=
  fderiv_update 0 y
