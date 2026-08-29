/-
Copyright (c) 2023 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, Patrick Massot
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# A collection of specific limit computations for `RCLike`

-/

public section

open Set Algebra Filter
open scoped Topology

namespace RCLike

variable (𝕜 : Type*) [RCLike 𝕜]

/--
theorem `tendsto_ofReal_cobounded_cobounded` / 定理 `tendsto_ofReal_cobounded_cobounded`

English:
theorem tendsto_ofReal_cobounded_cobounded
  proof: tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_norm_cobounded_atTop)

中文:
定理 tendsto_ofReal_cobounded_cobounded
  证明: tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_norm_cobounded_atTop)

Depends on / 依赖: mod_cast, tendsto_norm_atTop_iff_cobounded, tendsto_norm_atTop_iff_cobounded.mp, tendsto_norm_cobounded_atTop
-/
theorem tendsto_ofReal_cobounded_cobounded :
    Tendsto ofReal (Bornology.cobounded Real) (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_norm_cobounded_atTop)

/--
theorem `tendsto_ofReal_atTop_cobounded` / 定理 `tendsto_ofReal_atTop_cobounded`

English:
theorem tendsto_ofReal_atTop_cobounded
  proof: tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atTop_atTop)

中文:
定理 tendsto_ofReal_atTop_cobounded
  证明: tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atTop_atTop)

Depends on / 依赖: mod_cast, tendsto_abs_atTop_atTop, tendsto_norm_atTop_iff_cobounded, tendsto_norm_atTop_iff_cobounded.mp
-/
theorem tendsto_ofReal_atTop_cobounded :
    Tendsto ofReal atTop (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atTop_atTop)

/--
theorem `tendsto_ofReal_atBot_cobounded` / 定理 `tendsto_ofReal_atBot_cobounded`

English:
theorem tendsto_ofReal_atBot_cobounded
  proof: tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atBot_atTop)

中文:
定理 tendsto_ofReal_atBot_cobounded
  证明: tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atBot_atTop)

Depends on / 依赖: mod_cast, tendsto_abs_atBot_atTop, tendsto_norm_atTop_iff_cobounded, tendsto_norm_atTop_iff_cobounded.mp
-/
theorem tendsto_ofReal_atBot_cobounded :
    Tendsto ofReal atBot (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atBot_atTop)

end RCLike
