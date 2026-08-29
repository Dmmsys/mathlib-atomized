/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Max
public import Mathlib.Data.Set.CoeSort

/-!
# Maximal elements of subsets

Let `S : Set J` and `m : S`. If `m` is not a maximal element of `S`,
then `↑m : J` is not maximal in `J`.

-/

public section

universe u

namespace Set

variable {J : Type u} [Preorder J] {S : Set J} (m : S)

/--
lemma `not_isMax_coe` / 引理 `not_isMax_coe`

English:
lemma not_isMax_coe
  given: (hm : ¬ IsMax m)
  proof: fun h => hm (fun _ hb => h hb)

中文:
引理 not_isMax_coe
  条件: (hm : ¬ IsMax m)
  证明: fun h => hm (fun _ hb => h hb)
-/
lemma not_isMax_coe (hm : ¬ IsMax m) :
    ¬ IsMax m.1 :=
  fun h => hm (fun _ hb => h hb)

/--
lemma `not_isMin_coe` / 引理 `not_isMin_coe`

English:
lemma not_isMin_coe
  given: (hm : ¬ IsMin m)
  proof: fun h => hm (fun _ hb => h hb)

中文:
引理 not_isMin_coe
  条件: (hm : ¬ IsMin m)
  证明: fun h => hm (fun _ hb => h hb)
-/
lemma not_isMin_coe (hm : ¬ IsMin m) :
    ¬ IsMin m.1 :=
  fun h => hm (fun _ hb => h hb)

end Set
