/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Some lemmas on extended non-negative reals

These are some lemmas split off from `ENNReal.Basic` because they need a lot more imports.
They are probably good targets for further cleanup or moves.
-/

public section


open Function Set NNReal

variable {α : Type*}

namespace ENNReal

@[simp, norm_cast]
/-
**ENNReal.coe_indicator** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_indicator {α} (s : Set α) (f : α -> Real>=0) (a : α) : ((s.indicator f
 a : Real>=0) : Real>=0∞) = s.indicator (fun x => ↑(f x)) a
参数：s : Set α；f : α -> Real>=0；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_indicator`：∀ {α : Type u_1} {M : Type u_6} {N : Type u_7} {F : Type 
u_8} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass 
F M…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ≥0∞) = s.indicator (fun x => ↑(f x)) a :=
  map_indicator ofNNRealHom _ _ _

section Order

@[simp, norm_cast]
/-
**ENNReal.coe_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_finset_sup {s : Finset α} {f : α -> Real>=0} : ↑(s.sup f) = s.sup fun 
x => (f x : Real>=0∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp_of_linearOrder`：apply_sup_eq_sup_comp_of_li
nearOrder [SemilatticeSup β] [OrderBot β] (g : α -> β) (mono_g : Monotone g) (bo
t : g ⊥ = ⊥) : g (s.sup f) = s.su…
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
-/
theorem coe_finset_sup {s : Finset α} {f : α → ℝ≥0} : ↑(s.sup f) = s.sup fun x => (f x : ℝ≥0∞) :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder _ coe_mono rfl

end Order

end ENNReal

