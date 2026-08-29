/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Ring.Defs

/-!
# Centralizers of rings
-/

public section

assert_not_exists RelIso

variable {M : Type*} {S : Set M}

namespace Set

variable {a b}

@[simp]
/--
theorem `add_mem_centralizer` / 定理 `add_mem_centralizer`

English:
theorem add_mem_centralizer
  given: [Distrib M] (ha : a in centralizer S) (hb : b in centralizer S)
  proof: fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]

@[simp]

中文:
定理 add_mem_centralizer
  条件: [Distrib M] (ha : a in centralizer S) (hb : b in centralizer S)
  证明: fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]

@[simp]

Depends on / 依赖: add_mul, mul_add
-/
theorem add_mem_centralizer [Distrib M] (ha : a in centralizer S) (hb : b in centralizer S) :
    a + b in centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]

@[simp]
/--
theorem `neg_mem_centralizer` / 定理 `neg_mem_centralizer`

English:
theorem neg_mem_centralizer
  given: [Mul M] [HasDistribNeg M] (ha : a in centralizer S)
  proof: fun c hc => by rw [mul_neg, ha c hc, neg_mul]

中文:
定理 neg_mem_centralizer
  条件: [乘法 M] [有DistribNeg M] (ha : a in centralizer S)
  证明: fun c hc => by rw [mul_neg, ha c hc, neg_mul]

Depends on / 依赖: mul_neg, neg_mul
-/
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a in centralizer S) :
    -a in centralizer S := fun c hc => by rw [mul_neg, ha c hc, neg_mul]

end Set
